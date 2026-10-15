import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Pi
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Executable finite enumerations

Assignment enumeration uses sorted finite sets and the executable Cartesian
product of lists. The first coordinate is the most significant coordinate.
-/

namespace Counting.Algorithm.VariableElimination

universe u v w

/-- A canonical executable enumeration of a finite linearly ordered type. -/
def enumerateValues (α : Type u) [Fintype α] [LinearOrder α] : List α :=
  Finset.univ.sort (· ≤ ·)

@[simp] theorem mem_enumerateValues {α : Type u} [Fintype α] [LinearOrder α]
    (a : α) : a ∈ enumerateValues α := by
  simp [enumerateValues]

@[simp] theorem length_enumerateValues (α : Type u) [Fintype α] [LinearOrder α] :
    (enumerateValues α).length = Fintype.card α := by
  simp [enumerateValues]

@[simp] theorem nodup_enumerateValues (α : Type u) [Fintype α] [LinearOrder α] :
    (enumerateValues α).Nodup := by
  exact Finset.sort_nodup _ _

@[simp] theorem toFinset_enumerateValues (α : Type u) [Fintype α] [LinearOrder α] :
    (enumerateValues α).toFinset = Finset.univ := by
  ext a
  simp

/-- The executable list sum agrees with the finite mathematical sum. -/
theorem sum_enumerateValues {α : Type u} {R : Type w} [Fintype α] [LinearOrder α]
    [AddCommMonoid R] (f : α → R) :
    ((enumerateValues α).map f).sum = ∑ a, f a := by
  rw [← List.sum_toFinset f (nodup_enumerateValues α)]
  simp

/-- All assignments in the order of the Cartesian product of canonical lists. -/
def enumerateAssignments (α : Type u) (D : Type v)
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] : List (α → D) :=
  (List.pi (enumerateValues α) (fun _ => enumerateValues D)).map
    (fun f a => f a (mem_enumerateValues a))

@[simp] theorem mem_enumerateAssignments {α : Type u} {D : Type v}
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] (a : α → D) :
    a ∈ enumerateAssignments α D := by
  apply List.mem_map.mpr
  refine ⟨fun i _ => a i, ?_, rfl⟩
  exact (List.mem_pi _ _).mpr (fun i _ => mem_enumerateValues (a i))

private theorem length_pi_const {α : Type u} {D : Type v} [DecidableEq α]
    (xs : List α) (ds : List D) :
    (List.pi xs (fun _ => ds)).length = ds.length ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.pi_cons, List.length_flatMap, ih, Nat.pow_succ,
      Nat.mul_comm]

@[simp] theorem length_enumerateAssignments (α : Type u) (D : Type v)
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] :
    (enumerateAssignments α D).length = Fintype.card D ^ Fintype.card α := by
  simp [enumerateAssignments, length_pi_const]

@[simp] theorem toFinset_enumerateAssignments (α : Type u) (D : Type v)
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] :
    (enumerateAssignments α D).toFinset = Finset.univ := by
  ext a
  simp

@[simp] theorem nodup_enumerateAssignments (α : Type u) (D : Type v)
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] :
    (enumerateAssignments α D).Nodup := by
  apply (Multiset.toFinset_card_eq_card_iff_nodup
    (m := (enumerateAssignments α D : Multiset (α → D)))).mp
  simp

/-- Summing materialized assignment values agrees with finite-function summation. -/
theorem sum_enumerateAssignments {α : Type u} {D : Type v} {R : Type w}
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D]
    [AddCommMonoid R] (f : (α → D) → R) :
    ((enumerateAssignments α D).map f).sum = ∑ a, f a := by
  rw [← List.sum_toFinset f (nodup_enumerateAssignments α D)]
  simp

end Counting.Algorithm.VariableElimination
