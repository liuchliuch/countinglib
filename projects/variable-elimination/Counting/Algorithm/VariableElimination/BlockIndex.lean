import Mathlib.Data.List.Basic

/-! # Indexing equal-length list blocks -/

namespace Counting.Algorithm.VariableElimination

universe u v

/-- A flat map of equal-length blocks has the expected product length. -/
theorem length_flatMap_const {α : Type u} {β : Type v}
    (xs : List α) (f : α → List β) (m : Nat)
    (h : ∀ x ∈ xs, (f x).length = m) :
    (xs.flatMap f).length = xs.length * m := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
      simp [Nat.add_mul, Nat.add_comm]

/-- The row and in-block indices give a valid index into a uniform flat map. -/
theorem flatMap_const_index_lt {α : Type u} {β : Type v}
    (xs : List α) (f : α → List β) (m : Nat)
    (h : ∀ x ∈ xs, (f x).length = m)
    (i j : Nat) (hi : i < xs.length) (hj : j < m) :
    i * m + j < (xs.flatMap f).length := by
  rw [length_flatMap_const xs f m h]
  calc
    i * m + j < i * m + m := Nat.add_lt_add_left hj _
    _ = (i + 1) * m := by simp [Nat.add_mul]
    _ ≤ xs.length * m := Nat.mul_le_mul_right m hi

/-- Direct addressing into a list of equally sized blocks. -/
theorem getElem_flatMap_const {α : Type u} {β : Type v}
    (xs : List α) (f : α → List β) (m : Nat)
    (h : ∀ x ∈ xs, (f x).length = m)
    (i j : Nat) (hi : i < xs.length) (hj : j < m) :
    (xs.flatMap f)[i * m + j]'(flatMap_const_index_lt xs f m h i j hi hj) =
      (f xs[i])[j]'(by rw [h _ (List.mem_of_getElem (h := hi) rfl)]; exact hj) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
      have hx : (f x).length = m := h x (by simp)
      have ht : ∀ y ∈ xs, (f y).length = m := fun y hy => h y (by simp [hy])
      cases i with
      | zero =>
          simp only [Nat.zero_mul, Nat.zero_add, List.flatMap_cons, List.getElem_cons_zero]
          exact List.getElem_append_left (by omega)
      | succ i =>
          have hi' : i < xs.length := by simpa using hi
          simp only [List.flatMap_cons, List.getElem_cons_succ]
          rw [List.getElem_append_right (by rw [hx, Nat.add_mul]; omega)]
          have he : (i + 1) * m + j - (f x).length = i * m + j := by
            rw [hx, Nat.add_mul]
            omega
          simpa only [he] using ih ht i hi'

end Counting.Algorithm.VariableElimination
