import Mathlib.Data.List.FinRange
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
The replication compiler enumerates marked source rows in their original order.
These list lemmas identify a row's emitted ordinal with the number of earlier
marked rows and separate the marked and unmarked factors of a product.
-/

namespace Paper2.Paper1Proved.ReplicationOrdinals

variable {α β K : Type*}

/-- A marked row's ordinal lies in the filtered list. -/
theorem marked_rank_lt (p : α → Bool) (R : List α) (v : Fin R.length)
    (h : p (R.get v) = true) :
    ((R.take v.val).filter p).length < (R.filter p).length := by
  induction R with
  | nil => exact Fin.elim0 v
  | cons a R ih =>
      revert h
      refine Fin.cases ?_ (fun w => ?_) v
      · intro h
        have ha : p a = true := by simpa using h
        simp [ha]
      · intro h
        have hw : p (R.get w) = true := by simpa using h
        have hr := ih w hw
        cases ha : p a <;> simpa [List.filter_cons, ha] using hr

/-- Looking up the ordinal among earlier marked rows recovers the source row. -/
theorem get_marked_rank (p : α → Bool) (R : List α) (v : Fin R.length)
    (h : p (R.get v) = true) :
    (R.filter p).get ⟨((R.take v.val).filter p).length, marked_rank_lt p R v h⟩ =
      R.get v := by
  induction R with
  | nil => exact Fin.elim0 v
  | cons a R ih =>
      revert h
      refine Fin.cases ?_ (fun w => ?_) v
      · intro h
        have ha : p a = true := by simpa using h
        simp [List.get_eq_getElem, ha]
      · intro h
        have hw : p (R.get w) = true := by simpa using h
        cases ha : p a <;> simpa [List.get_eq_getElem, ha] using ih w hw

/-- Emit each row with the current marked ordinal and advance only on a mark. -/
def expand (p : α → Bool) (f : ℕ → α → β) (t : ℕ) : List α → List β
  | [] => []
  | a :: R => f t a :: expand p f (t + if p a then 1 else 0) R

/-- Recursive emission agrees with direct indexing by the earlier-mark count. -/
theorem expand_eq_indexed (p : α → Bool) (f : ℕ → α → β) (t : ℕ) (R : List α) :
    expand p f t R = (List.finRange R.length).map
      (fun v => f (t + ((R.take v.val).filter p).length) (R.get v)) := by
  induction R generalizing t with
  | nil => simp [expand]
  | cons a R ih =>
      simp only [List.length_cons, List.finRange_succ, List.map_cons, List.map_map,
        Function.comp_def, Fin.val_zero, Fin.val_succ, List.take_zero,
        List.take_succ_cons, List.filter_nil, List.length_nil, Nat.add_zero,
        List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [expand, ih]
      congr 1
      apply List.map_congr_left
      intro v _
      cases ha : p a <;>
        simp [ha, Nat.add_comm, Nat.add_left_comm]

private theorem expand_marked_prod [CommMonoid K] (p : α → Bool) (B : α → K)
    (F : ℕ → α → K) (t : ℕ) (R : List α) :
    (expand p (fun j a => if p a then F j a else B a) t R).prod =
      ((R.filter (fun a => !(p a))).map B).prod *
        ((List.finRange (R.filter p).length).map
          (fun j => F (t + j.val) ((R.filter p).get j))).prod := by
  induction R generalizing t with
  | nil => simp [expand]
  | cons a R ih =>
      cases ha : p a
      · have he : (a :: R).filter p = R.filter p := by simp [ha]
        rw [he]
        simpa [expand, ha, Nat.add_zero, mul_assoc] using
          congrArg (fun z => B a * z) (ih t)
      · have he : (a :: R).filter p = a :: R.filter p := by simp [ha]
        rw [he]
        simp only [expand, ha, ↓reduceIte, List.filter_cons, Bool.not_true,
          Bool.false_eq_true,
          List.map_cons, List.prod_cons, List.length_cons, List.finRange_succ,
          List.map_map, Function.comp_def, Fin.val_zero, Fin.val_succ,
          List.get_eq_getElem, List.getElem_cons_zero, List.getElem_cons_succ]
        rw [ih]
        simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm 1]
        ac_rfl

/-- Products over emitted rows split into unmarked factors and marked ordinals. -/
theorem indexed_marked_prod [CommMonoid K] (p : α → Bool) (R : List α)
    (B : α → K) (F : ℕ → α → K) :
    ((List.finRange R.length).map (fun v =>
      if p (R.get v) then F (((R.take v.val).filter p).length) (R.get v)
      else B (R.get v))).prod =
      ((R.filter (fun a => !(p a))).map B).prod *
        ∏ j : Fin (R.filter p).length, F j.val ((R.filter p).get j) := by
  simpa only [expand_eq_indexed, Nat.zero_add, Fin.prod_ofFn,
    ← List.ofFn_eq_map] using expand_marked_prod p B F 0 R

end Paper2.Paper1Proved.ReplicationOrdinals
