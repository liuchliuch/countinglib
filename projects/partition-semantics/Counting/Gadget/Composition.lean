import Counting.Model.Relabel
import Counting.Model.FiniteSums
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Literal composition and substitution of open instances

These are constructions on occurrence lists and variable types. Gluing retains
separate hidden-variable copies; hiding a boundary block reclassifies variables
by associativity of sums. A presentation stores an actual instance with finite
hidden indices, and substitution replaces every occurrence by a fresh copy of
its specified presentation.

The constructions and proof architecture adapt the read-only upstream modules
`ComplexCSP/Instances/Basic.lean`, `PresentationAlgorithms.lean`, and
`GadgetSubstitution.lean`. Here signatures may be nullary and the domain may be
empty. No equality or pinning signature is added to the language.
-/

namespace Counting.Gadget

open Counting.Model
open scoped BigOperators

variable {D R ι B C H H₁ H₂ : Type} {L : Language D R ι}

/-- Concatenate the two occurrence lists after giving the two hidden blocks
disjoint names. The boundary is shared, with its supplied order and repetitions. -/
def glue (I : OpenInstance L B H₁) (J : OpenInstance L B H₂) :
    OpenInstance L B (H₁ ⊕ H₂) :=
  ⟨(I.renameHidden Sum.inl).occurrences ++ (J.renameHidden Sum.inr).occurrences⟩

@[simp] theorem eval_glue [CommMonoid R] (I : OpenInstance L B H₁)
    (J : OpenInstance L B H₂) (a : B → D) (b : H₁ ⊕ H₂ → D) :
    (glue I J).eval a b = I.eval a (b ∘ Sum.inl) * J.eval a (b ∘ Sum.inr) := by
  simp only [OpenInstance.eval, glue, List.map_append, List.prod_append]
  exact congrArg₂ (· * ·)
    (OpenInstance.eval_renameHidden I (Sum.inl : H₁ → H₁ ⊕ H₂) a b)
    (OpenInstance.eval_renameHidden J (Sum.inr : H₂ → H₁ ⊕ H₂) a b)

/-- The partition tables of two actual independent hidden blocks multiply. -/
theorem partition_glue [CommSemiring R] [Fintype D]
    [Fintype H₁] [Fintype H₂] [DecidableEq H₁] [DecidableEq H₂]
    (I : OpenInstance L B H₁) (J : OpenInstance L B H₂) (a : B → D) :
    (glue I J).partition a = I.partition a * J.partition a := by
  simp only [OpenInstance.partition, eval_glue]
  exact FiniteSums.sum_independent_mul (I.eval a) (J.eval a)

/-- A disjoint union keeps both the boundary blocks and the hidden blocks
separate. In particular, isolated boundary variables remain in its type. -/
def disjointUnion (I : OpenInstance L B H₁) (J : OpenInstance L C H₂) :
    OpenInstance L (B ⊕ C) (H₁ ⊕ H₂) :=
  glue (I.renameBoundary Sum.inl) (J.renameBoundary Sum.inr)

@[simp] theorem eval_disjointUnion [CommMonoid R] (I : OpenInstance L B H₁)
    (J : OpenInstance L C H₂) (a : B ⊕ C → D) (b : H₁ ⊕ H₂ → D) :
    (disjointUnion I J).eval a b =
      I.eval (a ∘ Sum.inl) (b ∘ Sum.inl) *
        J.eval (a ∘ Sum.inr) (b ∘ Sum.inr) := by
  simp only [disjointUnion, eval_glue, OpenInstance.eval_renameBoundary]

/-- Independent open networks have the product partition table. -/
theorem partition_disjointUnion [CommSemiring R] [Fintype D]
    [Fintype H₁] [Fintype H₂] [DecidableEq H₁] [DecidableEq H₂]
    (I : OpenInstance L B H₁) (J : OpenInstance L C H₂) (a : B ⊕ C → D) :
    (disjointUnion I J).partition a =
      I.partition (a ∘ Sum.inl) * J.partition (a ∘ Sum.inr) := by
  simp only [disjointUnion, partition_glue, OpenInstance.partition_renameBoundary]

/-- Reclassify a boundary block as hidden, preserving all occurrences and ports. -/
def hideBoundary (I : OpenInstance L (B ⊕ H₁) H₂) :
    OpenInstance L B (H₁ ⊕ H₂) :=
  ⟨I.occurrences.map (fun c => c.rename (Equiv.sumAssoc B H₁ H₂))⟩

@[simp] theorem eval_hideBoundary [CommMonoid R]
    (I : OpenInstance L (B ⊕ H₁) H₂) (a : B → D) (b : H₁ ⊕ H₂ → D) :
    (hideBoundary I).eval a b =
      I.eval (Sum.elim a (b ∘ Sum.inl)) (b ∘ Sum.inr) := by
  simp only [OpenInstance.eval, hideBoundary, List.map_map]
  congr 2
  funext c
  simp only [Function.comp_apply, Occurrence.eval_rename]
  congr 1
  funext v
  rcases v with (v | v) | v <;> rfl

/-- Partial summation is implemented by hiding the selected boundary block. -/
theorem partition_hideBoundary [CommSemiring R] [Fintype D]
    [Fintype H₁] [Fintype H₂] [DecidableEq H₁] [DecidableEq H₂]
    (I : OpenInstance L (B ⊕ H₁) H₂) (a : B → D) :
    (hideBoundary I).partition a = ∑ b : H₁ → D, I.partition (Sum.elim a b) := by
  simp only [OpenInstance.partition, eval_hideBoundary]
  rw [FiniteSums.sum_sum_assignments]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr]

@[simp] theorem occurrences_length_glue (I : OpenInstance L B H₁)
    (J : OpenInstance L B H₂) :
    (glue I J).occurrences.length = I.occurrences.length + J.occurrences.length := by
  simp [glue, OpenInstance.renameHidden]

@[simp] theorem occurrences_length_hideBoundary (I : OpenInstance L (B ⊕ H₁) H₂) :
    (hideBoundary I).occurrences.length = I.occurrences.length := by
  simp [hideBoundary]

/-- An actual finite presentation of a boundary table. Hidden variables have
canonical finite indices, allowing independent copies to be constructed. -/
structure Presentation (L : Language D R ι) (B : Type) where
  hidden : Nat
  inst : OpenInstance L B (Fin hidden)

namespace Presentation

/-- Sum over every hidden variable of the stored instance. -/
def table [CommSemiring R] [Fintype D] (P : Presentation L B) : (B → D) → R :=
  P.inst.partition

/-- Rename boundary variables using an arbitrary map, including identifications. -/
def rename (P : Presentation L B) (f : B → C) : Presentation L C :=
  ⟨P.hidden, P.inst.renameBoundary f⟩

@[simp] theorem table_rename [CommSemiring R] [Fintype D]
    (P : Presentation L B) (f : B → C) (a : C → D) :
    (P.rename f).table a = P.table (a ∘ f) :=
  OpenInstance.partition_renameBoundary P.inst f a

/-- The empty occurrence list with no hidden variables. -/
def one : Presentation L B := ⟨0, ⟨[]⟩⟩

@[simp] theorem table_one [CommSemiring R] [Fintype D] (a : B → D) :
    (one : Presentation L B).table a = 1 := by
  exact OpenInstance.partition_of_isEmpty
    (OpenInstance.mk [] : OpenInstance L B (Fin 0)) a Fin.elim0

/-- Glue actual presentations, then encode their disjoint hidden blocks. -/
def mul (P Q : Presentation L B) : Presentation L B :=
  ⟨P.hidden + Q.hidden, (glue P.inst Q.inst).renameHidden finSumFinEquiv⟩

@[simp] theorem table_mul [CommSemiring R] [Fintype D]
    (P Q : Presentation L B) (a : B → D) :
    (P.mul Q).table a = P.table a * Q.table a := by
  unfold table mul
  rw [OpenInstance.partition_renameHidden_equiv, partition_glue]

/-- Recursively construct independent copies, including the empty product. -/
def product : List (Presentation L B) → Presentation L B
  | [] => one
  | P :: Ps => P.mul (product Ps)

@[simp] theorem table_product [CommSemiring R] [Fintype D]
    (Ps : List (Presentation L B)) (a : B → D) :
    (product Ps).table a = (Ps.map (fun P => P.table a)).prod := by
  induction Ps with
  | nil => simp [product]
  | cons P Ps ih => simp [product, ih]

/-- Hide a canonically indexed boundary block and recode the hidden sum. -/
def marginal {h : Nat} (P : Presentation L (B ⊕ Fin h)) : Presentation L B :=
  ⟨h + P.hidden, (hideBoundary P.inst).renameHidden finSumFinEquiv⟩

@[simp] theorem table_marginal [CommSemiring R] [Fintype D] {h : Nat}
    (P : Presentation L (B ⊕ Fin h)) (a : B → D) :
    P.marginal.table a = ∑ b : Fin h → D, P.table (Sum.elim a b) := by
  unfold marginal table
  rw [OpenInstance.partition_renameHidden_equiv, partition_hideBoundary]

@[simp] theorem hidden_rename (P : Presentation L B) (f : B → C) :
    (P.rename f).hidden = P.hidden := rfl

@[simp] theorem hidden_mul (P Q : Presentation L B) :
    (P.mul Q).hidden = P.hidden + Q.hidden := rfl

@[simp] theorem hidden_product (Ps : List (Presentation L B)) :
    (product Ps).hidden = (Ps.map Presentation.hidden).sum := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih => simp only [product, hidden_mul, List.map_cons, List.sum_cons, ih]

@[simp] theorem occurrences_length_rename (P : Presentation L B) (f : B → C) :
    (P.rename f).inst.occurrences.length = P.inst.occurrences.length := by
  simp [rename, OpenInstance.renameBoundary]

@[simp] theorem occurrences_length_mul (P Q : Presentation L B) :
    (P.mul Q).inst.occurrences.length =
      P.inst.occurrences.length + Q.inst.occurrences.length := by
  simp [mul, OpenInstance.renameHidden]

@[simp] theorem occurrences_length_product (Ps : List (Presentation L B)) :
    (product Ps).inst.occurrences.length =
      (Ps.map (fun P => P.inst.occurrences.length)).sum := by
  induction Ps with
  | nil => rfl
  | cons P Ps ih =>
    simp only [product, occurrences_length_mul, List.map_cons, List.sum_cons, ih]

end Presentation

namespace Substitution

variable {κ : Type} {M : Language D R κ}

/-- Specified base-language presentations, with the exact ordered arity of each
derived symbol. No realization property is built into this syntax. -/
abbrev Gadgets (L : Language D R ι) (M : Language D R κ) :=
  (j : κ) → Presentation L (Fin (M.arity j))

/-- Replace a single occurrence by its supplied gadget at the same ordered scope.
Repeated scope entries identify boundary variables, not hidden variables. -/
def atom (P : Gadgets L M) {V : Type} (c : Occurrence M V) : Presentation L V :=
  (P c.symbol).rename c.scope

/-- Copy all supplied gadgets independently, retaining every original variable
as a boundary variable until the final marginalization. -/
def expand (P : Gadgets L M) (I : OpenInstance M B H) : Presentation L (B ⊕ H) :=
  Presentation.product (I.occurrences.map (atom P))

/-- Literal substitution into an arbitrary open instance. Original hidden
variables and all fresh gadget variables are separate summation blocks. -/
def compile (P : Gadgets L M) (I : OpenInstance M B H) :
    OpenInstance L B (H ⊕ Fin (expand P I).hidden) :=
  hideBoundary (expand P I).inst

/-- The supplied finite presentations realize each individual source signature.
This is a local table equation, independent of any source instance or context. -/
def Realizes [CommSemiring R] [Fintype D] (P : Gadgets L M) : Prop :=
  ∀ j a, (P j).table a = M.value j a

@[simp] theorem table_atom [CommSemiring R] [Fintype D]
    (P : Gadgets L M) (hP : Realizes P) {V : Type}
    (c : Occurrence M V) (a : V → D) :
    (atom P c).table a = c.eval a := by
  rw [atom, Presentation.table_rename, hP]
  rfl

/-- Summing only the fresh gadget variables recovers the original occurrence
product for every fixed assignment, including unused original variables. -/
theorem table_expand [CommSemiring R] [Fintype D]
    (P : Gadgets L M) (hP : Realizes P) (I : OpenInstance M B H)
    (a : B → D) (b : H → D) :
    (expand P I).table (Sum.elim a b) = I.eval a b := by
  simp only [expand, Presentation.table_product, List.map_map, Function.comp_def,
    table_atom P hP]
  rfl

/-- Full partition preservation for actual substitution of every occurrence.
This holds over any commutative semiring, including exact cancellation when the
semiring is a ring, and requires no nonempty-domain or positive-arity premise. -/
theorem partition_compile [CommSemiring R] [Fintype D]
    [Fintype H] [DecidableEq H] (P : Gadgets L M) (hP : Realizes P)
    (I : OpenInstance M B H) (a : B → D) :
    (compile P I).partition a = I.partition a := by
  simp only [compile, partition_hideBoundary]
  change (∑ b : H → D, (expand P I).table (Sum.elim a b)) = I.partition a
  simp only [table_expand P hP, OpenInstance.partition]

/-- A canonical-output variant for source instances whose hidden block is `Fin h`. -/
def compilePresentation (P : Gadgets L M) {h : Nat}
    (I : OpenInstance M B (Fin h)) : Presentation L B :=
  (expand P I).marginal

@[simp] theorem table_compilePresentation [CommSemiring R] [Fintype D]
    (P : Gadgets L M) (hP : Realizes P) {h : Nat}
    (I : OpenInstance M B (Fin h)) (a : B → D) :
    (compilePresentation P I).table a = I.partition a := by
  simp only [compilePresentation, Presentation.table_marginal, table_expand P hP,
    OpenInstance.partition]

/-- Every occurrence gets its own finite block of fresh hidden variables. -/
theorem hidden_expand (P : Gadgets L M) (I : OpenInstance M B H) :
    (expand P I).hidden = (I.occurrences.map (fun c => (P c.symbol).hidden)).sum := by
  simp only [expand, Presentation.hidden_product, List.map_map, Function.comp_def,
    atom, Presentation.hidden_rename]

/-- Substitution retains the full sum of occurrence counts, even when the source
list repeats exactly the same labeled scope. -/
theorem occurrences_length_compile (P : Gadgets L M) (I : OpenInstance M B H) :
    (compile P I).occurrences.length =
      (I.occurrences.map (fun c => (P c.symbol).inst.occurrences.length)).sum := by
  simp only [compile, occurrences_length_hideBoundary, expand,
    Presentation.occurrences_length_product, List.map_map, Function.comp_def,
    atom, Presentation.occurrences_length_rename]

end Substitution
end Counting.Gadget
