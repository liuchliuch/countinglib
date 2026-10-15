import Counting.Algorithm.KarpLuby.MedianCost
import Counting.Algorithm.KarpLuby.ResourceBounds

/-!
# Selecting the group numerator before rational normalization

All groups use the same sample denominator. This executable selector therefore
compares natural numerators and performs only one final rational division. Its
value is proved equal to the unchanged R1 estimator, including zero samples,
zero groups, and repeated observations. The finite-vector access and natural
operations remain an intermediate model until compiled to stack programs.
-/
namespace Counting.Algorithm.KarpLubyMachine.NumeratorMedian

open Counting.Algorithm.KarpLuby
open Cost
open scoped BigOperators

/-- Indexed multiplicity is retained even when observed candidate values repeat. -/
def candidates (g : ℕ) (z : Fin g → ℕ) : Finset ℕ :=
  (Finset.univ.image z).filter fun a => g / 2 < (Finset.univ.filter fun i => z i ≤ a).card

theorem candidates_nonempty (g : ℕ) (z : Fin g → ℕ) (hg : 0 < g) :
    (candidates g z).Nonempty := by
  let V := Finset.univ.image z
  have hv : V.Nonempty := ⟨z ⟨0, hg⟩, Finset.mem_image.mpr ⟨⟨0, hg⟩, Finset.mem_univ _, rfl⟩⟩
  refine ⟨V.max' hv, Finset.mem_filter.mpr ⟨V.max'_mem hv, ?_⟩⟩
  have he : (Finset.univ.filter fun i => z i ≤ V.max' hv) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact V.le_max' _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  rw [he, Finset.card_univ, Fintype.card_fin]
  omega

/-- A proof-side finite-set specification, used to refine the recursive program. -/
def specification (g : ℕ) (z : Fin g → ℕ) : ℕ :=
  if hg : 0 < g then (candidates g z).min' (candidates_nonempty g z hg) else 0

/-- Each observation charges one vector access, one comparison, and an additional
increment precisely when it lies below the candidate. -/
def countBelow : (g : ℕ) → (Fin g → ℕ) → ℕ → Evaluation ℕ
  | 0, _, _ => ⟨0, 0⟩
  | g + 1, z, a =>
    let tail := countBelow g (fun i => z i.succ) a
    if z 0 ≤ a then ⟨tail.value + 1, tail.operations + 3⟩
    else ⟨tail.value, tail.operations + 2⟩

@[simp] theorem countBelow_value (g : ℕ) (z : Fin g → ℕ) (a : ℕ) :
    (countBelow g z a).value = (Finset.univ.filter fun i => z i ≤ a).card := by
  have hs : (countBelow g z a).value = ∑ i, if z i ≤ a then 1 else 0 := by
    induction g with
    | zero => simp [countBelow]
    | succ g ih =>
      simp only [countBelow, Fin.sum_univ_succ]
      split_ifs <;> simp [ih, Nat.add_comm]
  rw [hs]
  simp

theorem countBelow_operations_le (g : ℕ) (z : Fin g → ℕ) (a : ℕ) :
    (countBelow g z a).operations ≤ 3 * g := by
  induction g with
  | zero => simp [countBelow]
  | succ g ih =>
    have h := ih (fun i => z i.succ)
    simp only [countBelow]
    split <;> simp only <;> omega

def eligible (g : ℕ) (z : Fin g → ℕ) (a : ℕ) : Evaluation Bool :=
  let c := countBelow g z a
  ⟨decide (g / 2 < c.value), c.operations + 2⟩

@[simp] theorem eligible_value (g : ℕ) (z : Fin g → ℕ) (a : ℕ) :
    (eligible g z a).value = decide (g / 2 < (Finset.univ.filter fun i => z i ≤ a).card) := by
  simp [eligible]

def select (p : ℕ → Evaluation Bool) : List ℕ → Evaluation (Option ℕ)
  | [] => ⟨none, 0⟩
  | a :: as =>
    let tail := select p as
    let test := p a
    if test.value then
      ⟨some (tail.value.elim a (min a)), test.operations + tail.operations + 2⟩
    else ⟨tail.value, test.operations + tail.operations + 1⟩

@[simp] theorem select_value (p : ℕ → Evaluation Bool) (as : List ℕ) :
    (select p as).value = (as.filter fun a => (p a).value).min? := by
  induction as with
  | nil => rfl
  | cons a as ih =>
    simp only [select, List.filter_cons]
    cases (p a).value <;> simp [ih]

theorem select_operations_le (p : ℕ → Evaluation Bool) (as : List ℕ) (bound : ℕ)
    (h : ∀ a ∈ as, (p a).operations ≤ bound) :
    (select p as).operations ≤ as.length * (bound + 2) := by
  induction as with
  | nil => simp [select]
  | cons a as ih =>
    have ha := h a (by simp)
    have ht := ih (fun a ha => h a (by simp [ha]))
    simp only [select, List.length_cons]
    split <;> simp only <;> nlinarith

def collect : (g : ℕ) → (Fin g → ℕ) → Evaluation (List ℕ)
  | 0, _ => ⟨[], 0⟩
  | g + 1, z => let tail := collect g (fun i => z i.succ); ⟨z 0 :: tail.value, tail.operations + 2⟩

@[simp] theorem collect_value (g : ℕ) (z : Fin g → ℕ) :
    (collect g z).value = List.ofFn z := by
  induction g with
  | zero => rfl
  | succ g ih => simp [collect, ih, List.ofFn_succ]

@[simp] theorem collect_operations (g : ℕ) (z : Fin g → ℕ) :
    (collect g z).operations = 2 * g := by
  induction g with
  | zero => rfl
  | succ g ih => simp [collect, ih]; omega

/-- Natural-only executable upper median with an explicit quadratic comparison loop. -/
def median (g : ℕ) (z : Fin g → ℕ) : Evaluation ℕ :=
  let values := collect g z
  let chosen := select (eligible g z) values.value
  ⟨chosen.value.getD 0, values.operations + chosen.operations + 1⟩

@[simp] theorem median_value (g : ℕ) (z : Fin g → ℕ) :
    (median g z).value = specification g z := by
  by_cases hg : 0 < g
  · have hmem (a : ℕ) :
        a ∈ (List.ofFn z).filter (fun a => (eligible g z a).value) ↔ a ∈ candidates g z := by
      simp [candidates]
    have hm : specification g z ∈ candidates g z := by
      simp only [specification, dite_eq_left hg]
      exact Finset.min'_mem _ _
    have hmin : ((List.ofFn z).filter fun a => (eligible g z a).value).min? =
        some (specification g z) := by
      apply List.min?_eq_some_iff.mpr
      refine ⟨(hmem _).mpr hm, ?_⟩
      intro a ha
      simp only [specification, dite_eq_left hg]
      exact Finset.min'_le _ a ((hmem a).mp ha)
    simp only [median, collect_value, select_value, hmin, Option.getD_some]
  · have h : g = 0 := by omega
    subst g
    simp [median, collect, select, specification]

theorem median_operations_le (g : ℕ) (z : Fin g → ℕ) :
    (median g z).operations ≤ 2 * g + g * (3 * g + 4) + 1 := by
  have hp (a : ℕ) : (eligible g z a).operations ≤ 3 * g + 2 :=
    Nat.add_le_add_right (countBelow_operations_le g z a) 2
  have hs := select_operations_le (eligible g z) (List.ofFn z) (3 * g + 2) (fun a _ => hp a)
  simp only [List.length_ofFn] at hs
  simp only [median, collect_value, collect_operations]
  nlinarith

theorem median_observed (g : ℕ) (z : Fin g → ℕ) (hg : 0 < g) :
    ∃ i, (median g z).value = z i := by
  have hm : specification g z ∈ candidates g z := by
    simp only [specification, dite_eq_left hg]
    exact Finset.min'_mem _ _
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hm).1
  exact ⟨i, (median_value g z).trans hi.symm⟩

/-- Common positive denominators preserve every observed comparison. -/
theorem divided_le_iff (a b s : ℕ) (hs : 0 < s) :
    (a : ℚ) / s ≤ (b : ℚ) / s ↔ a ≤ b := by
  have hsq : (0 : ℚ) < s := by exact_mod_cast hs
  rw [div_le_div_iff_of_pos_right hsq]
  exact Nat.cast_le

theorem candidates_div (g : ℕ) (z : Fin g → ℕ) (s : ℕ) (hs : 0 < s) :
    medianCandidates g (fun i => (z i : ℚ) / s) =
      (candidates g z).image (fun a : ℕ => (a : ℚ) / s) := by
  ext q
  constructor
  · intro h
    obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hmem
    refine Finset.mem_image.mpr ⟨z i, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, ?_⟩
    simpa only [divided_le_iff _ _ s hs] using hc
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hmem, hc⟩ := Finset.mem_filter.mp ha
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, by rw [hi]⟩, ?_⟩
    simpa only [divided_le_iff _ _ s hs] using hc

/-- The executable natural median refines the original rational median. -/
theorem median_div (g : ℕ) (z : Fin g → ℕ) (s : ℕ) :
    KarpLuby.median g (fun i => (z i : ℚ) / s) = ((median g z).value : ℚ) / s := by
  by_cases hs : 0 < s
  · by_cases hg : 0 < g
    · have hmono : Monotone (fun a : ℕ => (a : ℚ) / s) := by
        intro a b hab
        exact (divided_le_iff a b s hs).mpr hab
      simp only [KarpLuby.median, median_value, specification, dite_eq_left hg]
      simp only [candidates_div g z s hs, Finset.min'_image hmono]
    · have h : g = 0 := by omega
      subst g
      simp [median, collect, select]
  · have h : s = 0 := by omega
    subst s
    simp only [Nat.cast_zero, div_zero]
    exact KarpLuby.median_all_zero g (fun _ => 0) (fun _ => rfl)

/-- Both clause and assignment reads are separate unit accesses. The fixed
branch pays for those two reads, Boolean equality, and conjunction. -/
def evalClause : {n : ℕ} → DNF.Clause n → DNF.Assignment n → Evaluation Bool
  | 0, _, _ => ⟨true, 0⟩
  | _ + 1, c, a =>
    let tail := evalClause (fun i => c i.succ) (fun i => a i.succ)
    match c 0 with
    | none => ⟨tail.value, tail.operations + 1⟩
    | some b => ⟨(a 0 == b) && tail.value, tail.operations + 4⟩

@[simp] theorem evalClause_value {n : ℕ} (c : DNF.Clause n) (a : DNF.Assignment n) :
    (evalClause c a).value = DNF.evalClause c a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [evalClause, DNF.evalClause]
    cases c 0 <;> simp [ih]

theorem evalClause_operations_le {n : ℕ} (c : DNF.Clause n) (a : DNF.Assignment n) :
    (evalClause c a).operations ≤ 4 * n := by
  induction n with
  | zero => simp [evalClause]
  | succ n ih =>
    have h := ih (fun i => c i.succ) (fun i => a i.succ)
    simp only [evalClause]
    cases c 0 <;> simp only <;> omega

def anyClause {n : ℕ} : List (DNF.Clause n) → DNF.Assignment n → Evaluation Bool
  | [], _ => ⟨false, 0⟩
  | c :: cs, a =>
    let test := evalClause c a
    if test.value then ⟨true, test.operations + 1⟩
    else
      let tail := anyClause cs a
      ⟨tail.value, test.operations + 1 + tail.operations⟩

@[simp] theorem anyClause_value {n : ℕ} (cs : List (DNF.Clause n)) (a : DNF.Assignment n) :
    (anyClause cs a).value = cs.any (fun c => DNF.evalClause c a) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [anyClause, evalClause_value, List.any_cons]
    cases DNF.evalClause c a <;> simp_all

theorem anyClause_operations_le {n : ℕ} (cs : List (DNF.Clause n)) (a : DNF.Assignment n) :
    (anyClause cs a).operations ≤ cs.length * (4 * n + 1) := by
  induction cs with
  | nil => simp [anyClause]
  | cons c cs ih =>
    have hc := evalClause_operations_le c a
    simp only [anyClause, List.length_cons]
    split <;> simp only <;> nlinarith

def owner {n : ℕ} (cs : List (DNF.Clause n)) (i : ℕ) (a : DNF.Assignment n) : Evaluation Bool :=
  let preceding := Cost.take i cs
  let found := anyClause preceding.value a
  ⟨!found.value, preceding.operations + found.operations + 1⟩

@[simp] theorem owner_value {n : ℕ} (cs : List (DNF.Clause n)) (i : ℕ) (a : DNF.Assignment n) :
    (owner cs i a).value = Program.owner cs i a := by simp [owner, Program.owner]

theorem owner_operations_le {n : ℕ} (cs : List (DNF.Clause n)) (i : ℕ) (a : DNF.Assignment n) :
    (owner cs i a).operations ≤ cs.length * (4 * n + 2) + 1 := by
  have ha := anyClause_operations_le (cs.take i) a
  have ht : (cs.take i).length ≤ cs.length := by simp only [List.length_take]; exact Nat.min_le_right _ _
  simp only [owner, Cost.take_operations, Cost.take_value]
  nlinarith

/-- The original selector and scale routines, with the corrected actual owner
scan. Repeated mass/scale work on successful trials remains explicitly charged. -/
def trial {n : ℕ} (cs : List (DNF.Clause n)) (r : ℕ) : Evaluation ℕ :=
  let selected := Cost.select cs r
  match selected.value with
  | none => ⟨0, selected.operations + 1⟩
  | some (i, a) =>
    let own := owner cs i a
    if own.value then
      let mass := Cost.totalMass cs
      let scale := Cost.dyadicScale mass.value
      ⟨scale.value, selected.operations + own.operations + mass.operations + scale.operations + 2⟩
    else ⟨0, selected.operations + own.operations + 2⟩

@[simp] theorem trial_value {n : ℕ} (cs : List (DNF.Clause n)) (r : ℕ) :
    (trial cs r).value = Program.trial cs r := by
  simp only [trial, Cost.select_value, Program.trial]
  cases Program.select cs r with
  | none => rfl
  | some p =>
    rcases p with ⟨i, a⟩
    simp only [owner_value]
    split <;> simp

def trialBound (n m : ℕ) : ℕ := m * (15 * n + 6) + 6 * (m + n + 1) + 4

theorem trial_operations_le {n : ℕ} (cs : List (DNF.Clause n)) (r : ℕ) :
    (trial cs r).operations ≤ trialBound n cs.length := by
  have hs := Cost.select_operations_le cs r
  have hm := Cost.totalMass_operations_le cs
  have hb := Cost.totalMass_size_le cs
  have hl : cs.length.size ≤ cs.length := Nat.size_le.mpr Nat.lt_two_pow_self
  unfold trialBound
  cases hv : (Cost.select cs r).value with
  | none => simp only [trial, hv]; nlinarith
  | some p =>
    rcases p with ⟨i, a⟩
    have ho := owner_operations_le cs i a
    simp only [trial, hv]
    split_ifs <;> simp only [Cost.dyadicScale_operations, Cost.totalMass_value] <;> nlinarith

/-- Width is a supplied, already computed natural. No total-mass/bit-length
expression occurs in the decoder call, including its implicit arguments. -/
def tapeTrialWithWidth {n : ℕ} (cs : List (DNF.Clause n)) (width : ℕ)
    (tape : CoinTape width) : Evaluation ℕ :=
  let word := Cost.decode width tape
  let answer := trial cs word.value
  ⟨answer.value, word.operations + answer.operations⟩

@[simp] theorem tapeTrialWithWidth_value {n : ℕ} (cs : List (DNF.Clause n)) (width : ℕ)
    (tape : CoinTape width) :
    (tapeTrialWithWidth cs width tape).value = Program.trial cs (decodeNat width tape) := by
  simp [tapeTrialWithWidth]

theorem tapeTrialWithWidth_operations_le {n : ℕ} (cs : List (DNF.Clause n)) (width : ℕ)
    (tape : CoinTape width) :
    (tapeTrialWithWidth cs width tape).operations ≤
      width * (width + 4) + trialBound n cs.length := by
  have hd := Cost.decode_operations_le width tape
  have ht := trial_operations_le cs (Cost.decode width tape).value
  simp only [tapeTrialWithWidth]
  omega

/-- A group retains the supplied width in every sample decoder and tape slice. -/
def groupNumeratorWithWidth {n : ℕ} (cs : List (DNF.Clause n)) (s width : ℕ)
    (tape : CoinTape (s * width)) : Evaluation ℕ :=
  Cost.sumVector s (fun i => tapeTrialWithWidth cs width
    (Program.coinChunk (width := width) (blocks := s) tape i))

@[simp] theorem groupNumeratorWithWidth_value {n : ℕ} (cs : List (DNF.Clause n)) (s width : ℕ)
    (tape : CoinTape (s * width)) :
    (groupNumeratorWithWidth cs s width tape).value =
      (List.ofFn fun i => Program.trial cs (decodeNat width
        (Program.coinChunk (width := width) tape i))).sum := by
  simp [groupNumeratorWithWidth]

theorem groupNumeratorWithWidth_operations_le {n : ℕ} (cs : List (DNF.Clause n)) (s width : ℕ)
    (tape : CoinTape (s * width)) :
    (groupNumeratorWithWidth cs s width tape).operations ≤
      s * (width * (width + 4) + trialBound n cs.length + 1) :=
  Cost.sumVector_operations_le s _ _ (fun _ => tapeTrialWithWidth_operations_le cs width _)

/-- Cache all natural group sums and select their median. The group-slice width
multiplication is computed once and charged once in addition to both loops. -/
def estimateWithWidth {n : ℕ} (cs : List (DNF.Clause n)) (s g width : ℕ)
    (tape : CoinTape (g * (s * width))) : Evaluation ℕ :=
  let groupWidth := s * width
  let groups := MedianCost.cacheVector g fun i => groupNumeratorWithWidth cs s width
    (Program.coinChunk (width := groupWidth) (blocks := g) tape i)
  let selected := median g groups.value
  ⟨selected.value, groups.operations + selected.operations + 1⟩

theorem estimateWithWidth_operations_le {n : ℕ} (cs : List (DNF.Clause n)) (s g width : ℕ)
    (tape : CoinTape (g * (s * width))) :
    (estimateWithWidth cs s g width tape).operations ≤
      g * (s * (width * (width + 4) + trialBound n cs.length + 1) + 2) +
      2 * g + g * (3 * g + 4) + 2 := by
  have hc := MedianCost.cacheVector_operations_le g
    (fun i => groupNumeratorWithWidth cs s width (Program.coinChunk tape i))
    _ (fun i => groupNumeratorWithWidth_operations_le cs s width _)
  have hm := median_operations_le g
    (MedianCost.cacheVector g
      (fun i => groupNumeratorWithWidth cs s width (Program.coinChunk tape i))).value
  simp only [estimateWithWidth]
  omega

/-- Only the final selected numerator requires rational division. -/
theorem estimateWithWidth_refines {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs s g)) :
    Program.estimate cs s g tape =
      ((estimateWithWidth cs s g (dyadicBits (Program.totalMass cs)) tape).value : ℚ) / s := by
  unfold Program.estimate
  have he (i : Fin g) : Program.groupAverage cs s (Program.coinChunk tape i) =
      ((groupNumeratorWithWidth cs s (dyadicBits (Program.totalMass cs))
        (Program.coinChunk tape i)).value : ℚ) / s := by
    simp [Program.groupAverage, Program.naturalAverage]
  simp only [he]
  rw [median_div]
  simp [estimateWithWidth]

/-- Width transport changes only proofs in finite tape indices. -/
private theorem estimateWithWidth_transport {n : ℕ} (cs : List (DNF.Clause n))
    (s g b c : ℕ) (h : b = c) (tape : CoinTape (g * (s * c))) :
    (estimateWithWidth cs s g b
      (fun i => tape ⟨i.val, by simpa only [h] using i.isLt⟩)).value =
      (estimateWithWidth cs s g c tape).value := by
  subst c
  rfl

/-- A standalone caller computes and charges mass and width once. The structured
request uses estimateWithWidth directly with its already charged prepared width. -/
def estimate {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs s g)) : Evaluation ℕ :=
  let mass := Cost.totalMass cs
  let width := Cost.bitLength mass.value
  let result := estimateWithWidth cs s g width.value (fun i => tape
    ⟨i.val, by simpa [width, mass, Program.randomBitBudget, dyadicBits] using i.isLt⟩)
  ⟨result.value, mass.operations + width.operations + result.operations⟩

@[simp] theorem estimate_value {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs s g)) :
    (estimate cs s g tape).value =
      (estimateWithWidth cs s g (dyadicBits (Program.totalMass cs)) tape).value := by
  have hw : (Cost.bitLength (Cost.totalMass cs).value).value =
      dyadicBits (Program.totalMass cs) := by simp [dyadicBits]
  exact estimateWithWidth_transport cs s g _ _ hw tape

theorem estimate_refines {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs s g)) :
    Program.estimate cs s g tape = ((estimate cs s g tape).value : ℚ) / s := by
  rw [estimate_value]
  exact estimateWithWidth_refines cs s g tape

/-- Actual selected numerator bit length, including empty groups and zero samples. -/
theorem estimate_size_le {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (tape : CoinTape (Program.randomBitBudget cs s g)) :
    (estimate cs s g tape).value.size ≤ s.size + cs.length.size + n + 2 := by
  rw [estimate_value]
  by_cases hg : 0 < g
  · obtain ⟨i, hi⟩ := median_observed g
      (fun i => (groupNumeratorWithWidth cs s (dyadicBits (Program.totalMass cs))
        (Program.coinChunk tape i)).value) hg
    simp only [estimateWithWidth, MedianCost.cacheVector_value]
    rw [hi, groupNumeratorWithWidth_value]
    exact Cost.sample_numerator_size_le cs s
      (fun j => decodeNat _ (Program.coinChunk (Program.coinChunk tape i) j))
  · have h : g = 0 := by omega
    subst g
    simp [estimateWithWidth, MedianCost.cacheVector, median, collect, select]

end Counting.Algorithm.KarpLubyMachine.NumeratorMedian
