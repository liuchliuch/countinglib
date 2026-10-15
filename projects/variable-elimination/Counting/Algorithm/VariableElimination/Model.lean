import Counting.Model.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Pi

namespace Counting.Algorithm.VariableElimination

/-- A scoped factor occurrence. The port map can repeat variables; zero ports
give a nullary factor. A list of these factors preserves multiplicities. -/
structure Factor (V D R : Type) where
  arity : Nat
  scope : Fin arity → V
  value : (Fin arity → D) → R

variable {V W D R : Type}

namespace Factor

def eval (f : Factor V D R) (a : V → D) : R := f.value (a ∘ f.scope)

def rename (f : Factor V D R) (r : V → W) : Factor W D R :=
  ⟨f.arity, r ∘ f.scope, f.value⟩

@[simp] theorem eval_rename (f : Factor V D R) (r : V → W) (a : W → D) :
    (f.rename r).eval a = f.eval (a ∘ r) := rfl

def support [DecidableEq V] (f : Factor V D R) : Finset V := Finset.univ.image f.scope

@[simp] theorem mem_support [DecidableEq V] (f : Factor V D R) (v : V) :
    v ∈ f.support ↔ ∃ i, f.scope i = v := by simp [support]

end Factor

def weight [CommMonoid R] (fs : List (Factor V D R)) (a : V → D) : R :=
  (fs.map (fun f => f.eval a)).prod

def partition [CommSemiring R] [Fintype V] [DecidableEq V] [Fintype D]
    (fs : List (Factor V D R)) : R := ∑ a : V → D, weight fs a

abbrev Remaining (v : V) := {w : V // w ≠ v}

def extend [DecidableEq V] (v : V) (d : D) (a : Remaining v → D) : V → D :=
  fun w => if h : w = v then d else a ⟨w, h⟩

@[simp] theorem extend_at [DecidableEq V] (v : V) (d : D) (a : Remaining v → D) :
    extend v d a v = d := by simp [extend]

@[simp] theorem extend_ne [DecidableEq V] (v : V) (d : D) (a : Remaining v → D)
    (w : Remaining v) : extend v d a w = a w := by simp [extend, w.property]

/-- Split the finite assignment sum without any inhabitance assumption on D. -/
theorem sum_extend [CommSemiring R] [Fintype V] [DecidableEq V] [Fintype D]
    (v : V) (f : (V → D) → R) :
    (∑ a : V → D, f a) = ∑ a : Remaining v → D, ∑ d : D, f (extend v d a) := by
  rw [← (Equiv.funSplitAt v D).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  congr 1
  funext a
  congr 1
  funext d
  congr 1
  funext w
  simp [Equiv.funSplitAt, Equiv.piSplitAt, extend]

end Counting.Algorithm.VariableElimination
