import Paper2.BellReduction.NativeSmoothing.Compile
import Paper2.BellReduction.ChargeBoundary

/-! Charge conservation on the original raw edge-end permutation. This also
covers punctures connected directly to one another, for which an ordinary
open network need not exist after deleting the designated rows. -/
namespace Paper2.BellReduction.RawCharge
open Complexity NativeSmoothing NativeSmoothing.Surgery

def bitCharge (b : Bool) : ℤ := if b then 1 else -1

def listCharge (xs : List Bool) : ℤ := (xs.map bitCharge).sum

@[simp] theorem bitCharge_not (b : Bool) : bitCharge (!b) = -bitCharge b := by
  cases b <;> rfl

@[simp] theorem listCharge_append (xs ys : List Bool) :
    listCharge (xs++ys) = listCharge xs + listCharge ys := by
  simp [listCharge]

theorem listCharge_ofFn {n : ℕ} (x : Fin n → Bool) :
    listCharge (List.ofFn x) = doubledCharge x := by
  have hb (b : Bool) : bitCharge b = 2*(b.toNat : ℤ)-1 := by cases b <;> rfl
  simp only [listCharge,List.map_ofFn,List.sum_ofFn]
  change (∑ i, bitCharge (x i)) = doubledCharge x
  simp_rw [hb]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  have hw : (∑ i : Fin n, ((x i).toNat : ℤ)) = (weight x : ℤ) := by
    unfold weight
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> rfl
  rw [hw]
  simp [doubledCharge]

/-- Every old edge contributes two opposite charges, even when both its ends
belong to the removed rows. -/
theorem edgeEnds_zero (m : ℕ) (c : ℕ → Bool) :
    listCharge ((edgeEnds 0 m).map (Choice.bit c)) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [ends_succ,List.map_append,listCharge_append,ih]
    simp only [List.map_cons,List.map_nil,listCharge,List.sum_cons,List.sum_nil,
      Choice.bit,Bool.false_eq_true,ite_false,ite_true,bitCharge_not]
    omega

/-- List form of charge across all remaining vertex tables. -/
theorem rows_charge (rows : List RawVertex) (c : ℕ → Bool) :
    listCharge (((rows.map Prod.snd).flatten).map (Choice.bit c)) =
      (rows.map (fun row => listCharge (row.2.map (Choice.bit c)))).sum := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    simp only [List.map_cons,List.flatten_cons,List.map_append,listCharge_append,List.sum_cons,ih]

/-- A general raw residual weight has divisible charge whenever each supported
remaining row has divisible charge. -/
theorem weight_charge {K : Type} [Field K] (T : Choice.Table K)
    (rows : List RawVertex) (c : ℕ → Bool)
    (hT : ∀ row ∈ rows, T row.1 (row.2.map (Choice.bit c)) ≠ 0 →
      (8 : ℤ) ∣ listCharge (row.2.map (Choice.bit c)))
    (hw : Choice.weight T c rows ≠ 0) :
    (8 : ℤ) ∣ (rows.map (fun row => listCharge (row.2.map (Choice.bit c)))).sum := by
  induction rows with
  | nil => exact dvd_zero _
  | cons row rows ih =>
    rw [Choice.weight_cons] at hw
    have hn := mul_ne_zero_iff.mp hw
    simp only [List.map_cons,List.sum_cons]
    exact dvd_add (hT row (by simp) hn.1)
      (ih (fun v hv => hT v (by simp [hv])) hn.2)

/-- The deleted endpoint block has charge divisible by eight without requiring
that deleting it leaves an ordinary-boundary graph. -/
theorem boundary_charge {K : Type} [Field K] (T : Choice.Table K)
    (m : ℕ) (boundary : List RawEndpoint) (rows : List RawVertex) (c : ℕ → Bool)
    (hp : (boundary ++ (rows.map Prod.snd).flatten).Perm (edgeEnds 0 m))
    (hT : ∀ row ∈ rows, T row.1 (row.2.map (Choice.bit c)) ≠ 0 →
      (8 : ℤ) ∣ listCharge (row.2.map (Choice.bit c)))
    (hw : Choice.weight T c rows ≠ 0) :
    (8 : ℤ) ∣ listCharge (boundary.map (Choice.bit c)) := by
  have hc := ((hp.map (Choice.bit c)).map bitCharge).sum_eq
  change listCharge ((boundary ++ (rows.map Prod.snd).flatten).map (Choice.bit c)) =
    listCharge ((edgeEnds 0 m).map (Choice.bit c)) at hc
  rw [List.map_append,listCharge_append,edgeEnds_zero,rows_charge] at hc
  have hd := weight_charge T rows c hT hw
  have he : listCharge (boundary.map (Choice.bit c)) =
      -(rows.map (fun row => listCharge (row.2.map (Choice.bit c)))).sum := by omega
  rw [he]
  exact dvd_neg.mpr hd

end Paper2.BellReduction.RawCharge
