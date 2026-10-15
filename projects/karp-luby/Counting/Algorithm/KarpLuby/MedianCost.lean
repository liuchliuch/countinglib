import Counting.Algorithm.KarpLuby.Cost

/-!
# An instrumented comparison implementation of the median

This evaluator scans the observed rational vector. Candidate membership is
counted with multiplicities, and a second recursion selects the least eligible
observed value. Its value agrees with the production finite-set median. The
cost bound counts rational comparisons and arithmetic as unit operations; it
does not assert their bit cost or a TM2 refinement.
-/
namespace Counting.Algorithm.KarpLuby.MedianCost

open Cost
open scoped BigOperators

/-- Count observations below a candidate by explicit finite-vector recursion. -/
def countBelow : (g : ℕ) → (Fin g → ℚ) → ℚ → Evaluation ℕ
  | 0, _, _ => ⟨0, 0⟩
  | g + 1, z, q =>
    let tail := countBelow g (fun i => z i.succ) q
    if z 0 ≤ q then ⟨tail.value + 1, tail.operations + 2⟩
    else ⟨tail.value, tail.operations + 1⟩

theorem countBelow_value_sum (g : ℕ) (z : Fin g → ℚ) (q : ℚ) :
    (countBelow g z q).value = ∑ i, if z i ≤ q then 1 else 0 := by
  induction g with
  | zero => simp [countBelow]
  | succ g ih =>
    simp only [countBelow, Fin.sum_univ_succ]
    split_ifs <;> simp [ih, Nat.add_comm]

@[simp] theorem countBelow_value (g : ℕ) (z : Fin g → ℚ) (q : ℚ) :
    (countBelow g z q).value = (Finset.univ.filter fun i => z i ≤ q).card := by
  rw [countBelow_value_sum]
  simp

theorem countBelow_operations_le (g : ℕ) (z : Fin g → ℚ) (q : ℚ) :
    (countBelow g z q).operations ≤ 2 * g := by
  induction g with
  | zero => simp [countBelow]
  | succ g ih =>
    have ht := ih (fun i => z i.succ)
    simp only [countBelow]
    split_ifs <;> simp only <;> omega

/-- Scan eligible values and retain their minimum. All costs come from the
executed predicate and list recursion, including a minimum comparison. -/
def selectMinimum (p : ℚ → Evaluation Bool) : List ℚ → Evaluation (Option ℚ)
  | [] => ⟨none, 0⟩
  | q :: qs =>
    let tail := selectMinimum p qs
    let accepted := p q
    if accepted.value then
      ⟨some (tail.value.elim q (min q)), accepted.operations + tail.operations + 2⟩
    else ⟨tail.value, accepted.operations + tail.operations + 1⟩

@[simp] theorem selectMinimum_value (p : ℚ → Evaluation Bool) (qs : List ℚ) :
    (selectMinimum p qs).value = (qs.filter fun q => (p q).value).min? := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    simp only [selectMinimum, List.filter_cons]
    cases (p q).value <;> simp [ih]

theorem selectMinimum_operations_le (p : ℚ → Evaluation Bool) (qs : List ℚ)
    (bound : ℕ) (h : ∀ q ∈ qs, (p q).operations ≤ bound) :
    (selectMinimum p qs).operations ≤ qs.length * (bound + 2) := by
  induction qs with
  | nil => simp [selectMinimum]
  | cons q qs ih =>
    have hq := h q (by simp)
    have ht := ih (fun q hq => h q (by simp [hq]))
    simp only [selectMinimum, List.length_cons]
    split_ifs <;> simp only <;> nlinarith

/-- Materialize the vector's candidate values, charging both access and cons. -/
def collect : (g : ℕ) → (Fin g → ℚ) → Evaluation (List ℚ)
  | 0, _ => ⟨[], 0⟩
  | g + 1, z =>
    let tail := collect g (fun i => z i.succ)
    ⟨z 0 :: tail.value, tail.operations + 2⟩

@[simp] theorem collect_value (g : ℕ) (z : Fin g → ℚ) :
    (collect g z).value = List.ofFn z := by
  induction g with
  | zero => rfl
  | succ g ih => simp [collect, ih, List.ofFn_succ]

@[simp] theorem collect_operations (g : ℕ) (z : Fin g → ℚ) :
    (collect g z).operations = 2 * g := by
  induction g with
  | zero => rfl
  | succ g ih => simp [collect, ih]; omega

/-- Eligibility costs the observed count and the threshold division/comparison. -/
def eligible (g : ℕ) (z : Fin g → ℚ) (q : ℚ) : Evaluation Bool :=
  let count := countBelow g z q
  ⟨decide (g / 2 < count.value), count.operations + 2⟩

@[simp] theorem eligible_value (g : ℕ) (z : Fin g → ℚ) (q : ℚ) :
    (eligible g z q).value = decide
      (g / 2 < (Finset.univ.filter fun i => z i ≤ q).card) := by
  simp [eligible]

theorem eligible_operations_le (g : ℕ) (z : Fin g → ℚ) (q : ℚ) :
    (eligible g z q).operations ≤ 2 * g + 2 := by
  exact Nat.add_le_add_right (countBelow_operations_le g z q) 2

/-- A concrete comparison-loop implementation of the radius-free upper median. -/
def median (g : ℕ) (z : Fin g → ℚ) : Evaluation ℚ :=
  let candidates := collect g z
  let selected := selectMinimum (eligible g z) candidates.value
  ⟨selected.value.getD 0, candidates.operations + selected.operations + 1⟩

/-- The loop and finite-set implementations compute exactly the same median,
including the empty-vector case and duplicate observation values. -/
@[simp] theorem median_value (g : ℕ) (z : Fin g → ℚ) :
    (median g z).value = KarpLuby.median g z := by
  by_cases hg : 0 < g
  · have hmem (q : ℚ) :
        q ∈ (List.ofFn z).filter (fun q => (eligible g z q).value) ↔
          q ∈ medianCandidates g z := by
      simp [medianCandidates]
    have hm : KarpLuby.median g z ∈ medianCandidates g z := by
      simp only [KarpLuby.median, dite_eq_left hg]
      exact Finset.min'_mem _ _
    have hmin : ((List.ofFn z).filter fun q => (eligible g z q).value).min? =
        some (KarpLuby.median g z) := by
      apply List.min?_eq_some_iff.mpr
      refine ⟨(hmem _).mpr hm, ?_⟩
      intro q hq
      simp only [KarpLuby.median, dite_eq_left hg]
      exact Finset.min'_le _ q ((hmem q).mp hq)
    simp only [median, collect_value, selectMinimum_value, hmin, Option.getD_some]
  · have hz : g = 0 := by omega
    subst g
    simp [median, collect, selectMinimum]

/-- Quadratic arithmetic/comparison bound for the recursive median program. -/
theorem median_operations_le (g : ℕ) (z : Fin g → ℚ) :
    (median g z).operations ≤ 2 * g + g * (2 * g + 4) + 1 := by
  have h := selectMinimum_operations_le (eligible g z) (List.ofFn z) (2 * g + 2)
    (fun q _ => eligible_operations_le g z q)
  simp only [List.length_ofFn] at h
  simp only [median, collect_operations, collect_value]
  nlinarith

/-- Evaluate a finite vector once and retain all of its values. The recursive
cost includes both the supplied computation and constructing its stored slot. -/
def cacheVector {α : Type} : (g : ℕ) → (Fin g → Evaluation α) → Evaluation (Fin g → α)
  | 0, _ => ⟨Fin.elim0, 0⟩
  | g + 1, f =>
    let first := f 0
    let tail := cacheVector g (fun i => f i.succ)
    ⟨Fin.cons first.value tail.value, first.operations + tail.operations + 2⟩

@[simp] theorem cacheVector_value {α : Type} (g : ℕ) (f : Fin g → Evaluation α) :
    (cacheVector g f).value = fun i => (f i).value := by
  induction g with
  | zero => funext i; exact Fin.elim0 i
  | succ g ih =>
    simp only [cacheVector, ih]
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

theorem cacheVector_operations_le {α : Type} (g : ℕ) (f : Fin g → Evaluation α)
    (bound : ℕ) (h : ∀ i, (f i).operations ≤ bound) :
    (cacheVector g f).operations ≤ g * (bound + 2) := by
  induction g with
  | zero => simp [cacheVector]
  | succ g ih =>
    have h0 := h 0
    have ht := ih (fun i => f i.succ) (fun i => h i.succ)
    simp only [cacheVector]
    nlinarith

/-- A complete instrumented evaluator on normalized clauses: evaluate each
independent group once, then run the concrete comparison median. This cost model
charges stored-vector access as one primitive; it does not refine function-based
vectors or clause-update chains to a finite-machine representation. -/
def estimate {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs s g)) : Evaluation ℚ :=
  let groups := cacheVector g fun i => Cost.groupAverage cs s (Program.coinChunk tape i)
  let selected := median g groups.value
  ⟨selected.value, groups.operations + selected.operations⟩

/-- The instrumented evaluator returns the exact production estimator value,
for every normalized DNF, sample/group count, and finite Boolean tape. -/
@[simp] theorem estimate_value {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs s g)) :
    (estimate cs s g tape).value = Program.estimate cs s g tape := by
  simp [estimate, Program.estimate]

/-- Explicit polynomial arithmetic/access bound for the complete instrumented
normalized estimator. Normalization, codecs, primitive bit-time and the TM2
refinement remain separate obligations. -/
theorem estimate_operations_le {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs s g)) :
    (estimate cs s g tape).operations ≤
      g * (s * ((cs.length + n + 1) * (cs.length + n + 5) +
        cs.length * (14 * n + 6) + 6 * (cs.length + n + 1) + 5) + 3) +
      2 * g + g * (2 * g + 4) + 1 := by
  have hc := cacheVector_operations_le g
    (fun i => Cost.groupAverage cs s (Program.coinChunk tape i)) _
    (fun i => Cost.groupAverage_operations_le cs s (Program.coinChunk tape i))
  have hm := median_operations_le g
    (cacheVector g fun i => Cost.groupAverage cs s (Program.coinChunk tape i)).value
  simp only [estimate]
  nlinarith

end Counting.Algorithm.KarpLuby.MedianCost
