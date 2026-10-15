import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum

/-!
# Finite weighted occurrence semantics

An occurrence has a label and an ordered scope. Scopes may repeat variables, and
lists retain repeated occurrences. Boundary variables are assigned externally;
hidden variables are summed over by the partition table. Variable types retain
isolated variables, even when no scope uses them.

The table and occurrence conventions follow `ComplexCSP/Instances/Basic.lean`.
The present interface also permits nullary signatures and empty domains. It does
not add equality, pinning, or any other signature to a supplied language.
-/

namespace Counting.Model

/-- A table with `n` ordered input ports. The case `n = 0` is permitted. -/
abbrev Signature (D R : Type) (n : Nat) := (Fin n → D) → R

/-- A family of signature tables, indexed by labels. A `Fintype` instance on the
label type expresses finiteness; no positivity or nonzero-value condition is
imposed on the tables. -/
structure Language (D R ι : Type) where
  arity : ι → Nat
  value : (i : ι) → Signature D R (arity i)

/-- A finite language with canonical finite labels, including the empty language. -/
structure FiniteLanguage (D R : Type) where
  size : Nat
  language : Language D R (Fin size)

/-- A labeled occurrence with an ordered scope that may repeat variables. -/
structure Occurrence {D R ι : Type} (L : Language D R ι) (V : Type) where
  symbol : ι
  scope : Fin (L.arity symbol) → V

namespace Occurrence

variable {D R ι V W X : Type} {L : Language D R ι}

/-- Apply a variable map to every port, retaining the label and port order. -/
def rename (c : Occurrence L V) (f : V → W) : Occurrence L W :=
  ⟨c.symbol, f ∘ c.scope⟩

/-- Evaluate the table at the tuple selected by this occurrence's ordered scope. -/
def eval (c : Occurrence L V) (a : V → D) : R :=
  L.value c.symbol (a ∘ c.scope)

@[simp] theorem rename_id (c : Occurrence L V) : c.rename id = c := rfl

@[simp] theorem rename_rename (c : Occurrence L V) (f : V → W) (g : W → X) :
    (c.rename f).rename g = c.rename (g ∘ f) := rfl

/-- Pulling an assignment back along a variable map commutes with evaluation. -/
@[simp] theorem eval_rename (c : Occurrence L V) (f : V → W) (a : W → D) :
    (c.rename f).eval a = c.eval (a ∘ f) := rfl

end Occurrence

/-- An open instance with boundary variables `B` and hidden variables `H`.
The occurrence list retains multiplicities, including repeated nullary factors. -/
structure OpenInstance {D R ι : Type} (L : Language D R ι) (B H : Type) where
  occurrences : List (Occurrence L (B ⊕ H))

namespace OpenInstance

variable {D R ι B H : Type} {L : Language D R ι}

/-- Multiply all occurrence values at the combined boundary and hidden assignment. -/
def eval [CommMonoid R] (I : OpenInstance L B H) (a : B → D) (b : H → D) : R :=
  (I.occurrences.map (fun c => c.eval (Sum.elim a b))).prod

/-- The pinned partition table, summing over every hidden-variable assignment.
This includes assignments to isolated variables and allows exact cancellation. -/
def partition [CommSemiring R] [Fintype D] [Fintype H] [DecidableEq H]
    (I : OpenInstance L B H) (a : B → D) : R :=
  ∑ b : H → D, I.eval a b

@[simp] theorem eval_nil [CommMonoid R] (a : B → D) (b : H → D) :
    (OpenInstance.mk [] : OpenInstance L B H).eval a b = 1 := rfl

@[simp] theorem eval_cons [CommMonoid R] (c : Occurrence L (B ⊕ H))
    (cs : List (Occurrence L (B ⊕ H))) (a : B → D) (b : H → D) :
    (OpenInstance.mk (c :: cs) : OpenInstance L B H).eval a b =
      c.eval (Sum.elim a b) * (OpenInstance.mk cs : OpenInstance L B H).eval a b := rfl

/-- Unfold the partition table as its finite sum of assignment values. -/
theorem partition_eq_sum [CommSemiring R] [Fintype D] [Fintype H] [DecidableEq H]
    (I : OpenInstance L B H) (a : B → D) :
    I.partition a = ∑ b : H → D, I.eval a b := rfl

end OpenInstance
end Counting.Model
