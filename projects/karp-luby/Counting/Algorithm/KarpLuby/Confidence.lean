import Counting.Algorithm.KarpLuby.Imported.Concentration
import Counting.Algorithm.KarpLuby.Imported.Amplification

/-!
# Confidence bounds for the Karp–Luby estimator

The finite-product probability calculus is reused from the pinned Hidden Circuits
sources. The median below is executable and needs no unknown target value or
error radius. Its finite selection rule includes repeated observations through
index counts, even though candidate *values* are stored in a finite set.
-/
namespace Counting.Algorithm.KarpLuby

open HiddenCircuits.Approximation.SelfReduction
open scoped BigOperators

/-- Observed values with strictly more than half the observations below them. -/
def medianCandidates (g : ℕ) (z : Fin g → ℚ) : Finset ℚ :=
  (Finset.univ.image z).filter fun q => g / 2 <
    (Finset.univ.filter fun i => z i ≤ q).card

 theorem medianCandidates_nonempty (g : ℕ) (z : Fin g → ℚ) (hg : 0 < g) :
    (medianCandidates g z).Nonempty := by
  let V := Finset.univ.image z
  have hv : V.Nonempty := ⟨z ⟨0, hg⟩, Finset.mem_image.mpr ⟨⟨0, hg⟩, Finset.mem_univ _, rfl⟩⟩
  refine ⟨V.max' hv, Finset.mem_filter.mpr ⟨V.max'_mem hv, ?_⟩⟩
  have he : (Finset.univ.filter fun i => z i ≤ V.max' hv) = Finset.univ := by
    apply Finset.filter_eq_self.mpr
    intro i hi
    exact V.le_max' _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  rw [he, Finset.card_univ, Fintype.card_fin]
  omega

/-- Total, rational-valued upper median; the empty observation vector returns zero. -/
def median (g : ℕ) (z : Fin g → ℚ) : ℚ :=
  if hg : 0 < g then (medianCandidates g z).min' (medianCandidates_nonempty g z hg)
  else 0

@[simp] theorem median_zero (z : Fin 0 → ℚ) : median 0 z = 0 := by
  simp [median]

/-- A nonempty median is one of its rational input observations. -/
 theorem median_eq_observation (g : ℕ) (z : Fin g → ℚ) (hg : 0 < g) :
    ∃ i, median g z = z i := by
  have hm : median g z ∈ medianCandidates g z := by
    simp only [median, dite_eq_left hg]
    exact Finset.min'_mem _ _
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hm).1
  exact ⟨i, hi.symm⟩

 theorem median_nonneg (g : ℕ) (z : Fin g → ℚ) (hz : ∀ i, 0 ≤ z i) :
    0 ≤ median g z := by
  by_cases hg : 0 < g
  · obtain ⟨i, hi⟩ := median_eq_observation g z hg
    rw [hi]
    exact hz i
  · simp [median, hg]

 theorem median_all_zero (g : ℕ) (z : Fin g → ℚ) (hz : ∀ i, z i = 0) :
    median g z = 0 := by
  by_cases hg : 0 < g
  · obtain ⟨i, hi⟩ := median_eq_observation g z hg
    exact hi.trans (hz i)
  · simp [median, hg]

/-- A strict majority of accurate observations forces the radius-free median to
be accurate with the same radius. -/
 theorem median_accurate (g : ℕ) (z : Fin g → ℚ) (C radius : ℚ)
    (hmajor : g < 2 * (Finset.univ.filter fun i => |z i - C| ≤ radius).card) :
    |median g z - C| ≤ radius := by
  have hg : 0 < g := by
    by_contra h
    have hz : g = 0 := by omega
    subst g
    simp at hmajor
  let G := Finset.univ.filter fun i => |z i - C| ≤ radius
  have hG : G.Nonempty := Finset.card_pos.mp (by dsimp [G]; omega)
  have hGV : (G.image z).Nonempty := hG.image z
  let u := (G.image z).max' hGV
  have hu : u ∈ G.image z := (G.image z).max'_mem hGV
  obtain ⟨j, hj, hjv⟩ := Finset.mem_image.mp hu
  have hup : u ≤ C + radius := by
    have ha := (abs_le.mp (Finset.mem_filter.mp hj).2).2
    rw [hjv] at ha
    linarith
  have huCand : u ∈ medianCandidates g z := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hjv⟩, ?_⟩
    have hsub : G ⊆ Finset.univ.filter fun i => z i ≤ u := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (G.image z).le_max' _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)⟩
    have hc := Finset.card_le_card hsub
    dsimp [G] at hc
    omega
  have hmed : median g z ∈ medianCandidates g z := by
    simp only [median, dite_eq_left hg]
    exact Finset.min'_mem _ _
  have hupper : median g z ≤ C + radius := by
    apply le_trans _ hup
    simp only [median, dite_eq_left hg]
    exact Finset.min'_le _ _ huCand
  have hlower : C - radius ≤ median g z := by
    by_contra h
    have hm : median g z < C - radius := lt_of_not_ge h
    let L := Finset.univ.filter fun i => z i ≤ median g z
    have hL : g / 2 < L.card := (Finset.mem_filter.mp hmed).2
    have hdis : Disjoint L G := by
      apply Finset.disjoint_left.mpr
      intro i hiL hiG
      have hi := (Finset.mem_filter.mp hiL).2
      have hi' := (abs_le.mp (Finset.mem_filter.mp hiG).2).1
      linarith
    have hc : L.card + G.card ≤ g := by
      rw [← Finset.card_union_of_disjoint hdis]
      exact (Finset.card_le_card (Finset.subset_univ (L ∪ G))).trans_eq (by simp)
    dsimp [G] at hc
    omega
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Relative Chebyshev for a finite estimator whose second moment has the
Karp–Luby bound. No bounded-in-[0,1] assumption loses an extra cover factor. -/
 theorem sampleAverage_relative_failure {α : Type*} [Fintype α] [Nonempty α]
    (X : α → ℚ) (C : ℚ) (m n : ℕ) (ε : ℚ)
    (hmean : mean X = C)
    (hsecond : mean (fun a => X a ^ 2) ≤ 2 * (m : ℚ) * C ^ 2)
    (hC : 0 < C) (hn : 0 < n) (hε : 0 < ε)
    (hbudget : 144 * (m : ℚ) ≤ (n : ℚ) * ε ^ 2) :
    probability (fun r : Fin n → α => ε * C / 3 < |sampleAverage n X r - C|) ≤ 1 / 8 := by
  have hr : 0 < ε * C / 3 := by positivity
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hv : mean (fun a => (X a - C) ^ 2) ≤ 2 * (m : ℚ) * C ^ 2 := by
    rw [← hmean, mean_centered_sq, hmean]
    nlinarith [sq_nonneg C]
  have hm := probability_markov (fun r : Fin n → α => (sampleAverage n X r - C) ^ 2)
    (fun _ => sq_nonneg _) ((ε * C / 3) ^ 2) (sq_pos_of_pos hr)
  have hs : probability (fun r : Fin n → α => ε * C / 3 < |sampleAverage n X r - C|) ≤
      probability (fun r : Fin n → α => (ε * C / 3) ^ 2 ≤ (sampleAverage n X r - C) ^ 2) := by
    apply probability_mono
    intro r h
    nlinarith [sq_abs (sampleAverage n X r - C), abs_nonneg (sampleAverage n X r - C)]
  apply hs.trans (hm.trans _)
  rw [← hmean, sampleAverage_variance X n hn, hmean]
  calc
    _ ≤ (2 * (m : ℚ) * C ^ 2 / n) / (ε * C / 3) ^ 2 := by
      exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hv hnq.le) (sq_nonneg _)
    _ ≤ 1 / 8 := by
      apply (div_le_iff₀ (sq_pos_of_pos hr)).2
      apply (div_le_iff₀ hnq).2
      nlinarith [mul_le_mul_of_nonneg_right hbudget (sq_nonneg C)]

/-- The implemented confidence amplifier: independent group averages followed
by a median whose rule is independent of the unknown answer. -/
def amplifiedEstimate {α : Type*} (X : α → ℚ) (n k : ℕ)
    (r : Fin (2 * k) → Fin n → α) : ℚ :=
  median (2 * k) (fun i => sampleAverage n X (r i))

/-- Every tape yields exactly zero whenever each trial does. -/
 theorem amplifiedEstimate_zero {α : Type*} (X : α → ℚ) (n k : ℕ)
    (hX : ∀ a, X a = 0) (r : Fin (2 * k) → Fin n → α) :
    amplifiedEstimate X n k r = 0 := by
  apply median_all_zero
  intro i
  simp [sampleAverage, hX]

 theorem amplifiedEstimate_nonneg {α : Type*} (X : α → ℚ) (n k : ℕ)
    (hX : ∀ a, 0 ≤ X a) (r : Fin (2 * k) → Fin n → α) :
    0 ≤ amplifiedEstimate X n k r := by
  apply median_nonneg
  intro i
  exact div_nonneg (Finset.sum_nonneg fun j _ => hX (r i j)) (Nat.cast_nonneg n)

/-- Full relative-error guarantee, with arbitrary positive rational ε and
failure at most 2⁻ᵏ on a genuine finite product of independent observations. -/
 theorem amplifiedEstimate_failure {α : Type*} [Fintype α] [Nonempty α]
    (X : α → ℚ) (C : ℚ) (m n k : ℕ) (ε : ℚ)
    (hmean : mean X = C)
    (hsecond : mean (fun a => X a ^ 2) ≤ 2 * (m : ℚ) * C ^ 2)
    (hC : 0 < C) (hn : 0 < n) (hε : 0 < ε)
    (hbudget : 144 * (m : ℚ) ≤ (n : ℚ) * ε ^ 2) :
    probability (fun r : Fin (2 * k) → Fin n → α =>
      ε * C < |amplifiedEstimate X n k r - C|) ≤ 1 / (2 ^ k : ℚ) := by
  classical
  let E := fun r : Fin n → α => ε * C / 3 < |sampleAverage n X r - C|
  have hE : probability E ≤ 1 / 8 :=
    sampleAverage_relative_failure X C m n ε hmean hsecond hC hn hε hbudget
  apply (probability_mono (F := fun r : Fin (2 * k) → Fin n → α =>
    k ≤ (Finset.univ.filter fun i => E (r i)).card) ?_).trans (majority_failure_bound E hE k)
  intro r hr
  by_contra hbad
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (2 * k)))) (p := fun i => E (r i))
  have hgood : 2 * k < 2 * (Finset.univ.filter fun i =>
      |sampleAverage n X (r i) - C| ≤ ε * C / 3).card := by
    simp only [E, not_lt, Finset.card_univ, Fintype.card_fin] at hsplit
    dsimp [E] at hbad
    omega
  have ha := median_accurate (2 * k) (fun i => sampleAverage n X (r i)) C (ε * C / 3) hgood
  change |amplifiedEstimate X n k r - C| ≤ ε * C / 3 at ha
  have hpos : 0 < ε * C := mul_pos hε hC
  linarith

/-- The equivalent PAC success-probability form. -/
 theorem amplifiedEstimate_success {α : Type*} [Fintype α] [Nonempty α]
    (X : α → ℚ) (C : ℚ) (m n k : ℕ) (ε : ℚ)
    (hmean : mean X = C)
    (hsecond : mean (fun a => X a ^ 2) ≤ 2 * (m : ℚ) * C ^ 2)
    (hC : 0 < C) (hn : 0 < n) (hε : 0 < ε)
    (hbudget : 144 * (m : ℚ) ≤ (n : ℚ) * ε ^ 2) :
    1 - 1 / (2 ^ k : ℚ) ≤ probability (fun r : Fin (2 * k) → Fin n → α =>
      |amplifiedEstimate X n k r - C| ≤ ε * C) := by
  have hf := amplifiedEstimate_failure X C m n k ε hmean hsecond hC hn hε hbudget
  have hc := probability_compl (fun r : Fin (2 * k) → Fin n → α =>
    ε * C < |amplifiedEstimate X n k r - C|)
  simp only [not_lt] at hc
  linarith

/-- Unary inverse-accuracy sample budget, polynomial in cover size and r. -/
def groupSize (m r : ℕ) : ℕ := 144 * m * (r + 1) ^ 2

 theorem groupSize_pos (m r : ℕ) (hm : 0 < m) : 0 < groupSize m r := by
  unfold groupSize
  positivity

 theorem groupSize_budget (m r : ℕ) :
    144 * (m : ℚ) ≤ (groupSize m r : ℚ) * (1 / ((r : ℚ) + 1)) ^ 2 := by
  have hr : (r : ℚ) + 1 ≠ 0 := by positivity
  unfold groupSize
  push_cast
  field_simp
  exact le_rfl

 theorem amplifiedEstimate_inverse_accuracy {α : Type*} [Fintype α] [Nonempty α]
    (X : α → ℚ) (C : ℚ) (m r k : ℕ)
    (hmean : mean X = C)
    (hsecond : mean (fun a => X a ^ 2) ≤ 2 * (m : ℚ) * C ^ 2)
    (hC : 0 < C) (hm : 0 < m) :
    probability (fun tapes : Fin (2 * k) → Fin (groupSize m r) → α =>
      C / ((r : ℚ) + 1) < |amplifiedEstimate X (groupSize m r) k tapes - C|) ≤
        1 / (2 ^ k : ℚ) := by
  simpa only [one_div_mul_eq_div] using
    amplifiedEstimate_failure X C m (groupSize m r) k (1 / ((r : ℚ) + 1))
      hmean hsecond hC (groupSize_pos m r hm) (by positivity) (groupSize_budget m r)

end Counting.Algorithm.KarpLuby
