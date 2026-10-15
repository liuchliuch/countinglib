import ComplexCSP.Algebra.PowerSums

/-!
# Bounded simultaneous row-detector exponents

An alternative to the paper's use of Skolem--Mahler--Lech in row detection.
The standalone finite-zero-set assertion of Lemma 8.3 is not proved here.
Instead, tensoring the finite families and grouping equal bases supplies a
nonzero weighted exponential sum. A finite Vandermonde block finds a witness.
-/

namespace ComplexCSP.RowDetector

open scoped BigOperators

/-- Every root of unity in the field is killed by this exponent. Existence of
such an exponent for number fields is a separate theorem, not assumed proved. -/
def KillsTorsion (K : Type*) [Monoid K] (E : ℕ) : Prop :=
  ∀ x : K, IsOfFinOrder x → x ^ E = 1

/-- Raising to a positive power is injective on nonzero `E`th powers when `E`
kills all roots of unity in the field. -/
theorem pow_injective_on_torsion_killing_powers {K : Type*} [Field K]
    (E L : ℕ) (hE : 0 < E) (hL : 0 < L) (hkill : KillsTorsion K E)
    (x y : K) (_hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : (x ^ E) ^ L = (y ^ E) ^ L) : x ^ E = y ^ E := by
  have ht : IsOfFinOrder (x / y) := by
    apply isOfFinOrder_iff_pow_eq_one.mpr
    refine ⟨E * L, Nat.mul_pos hE hL, ?_⟩
    simp only [pow_mul, div_pow]
    rw [hxy, div_self (pow_ne_zero L (pow_ne_zero E hy))]
  have hroot := hkill (x / y) ht
  rw [div_pow, div_eq_one_iff_eq (pow_ne_zero E hy)] at hroot
  exact hroot

/-- A finite indexed multiset whose `L`th powers have no collisions except equal
values has a nonzero power sum at some exponent `1 + L*t`, with `t < card ι`.
Repeated values have positive integer multiplicity; they do not cancel. -/
theorem exists_powerSum_one_add_mul {ι K : Type*} [Fintype ι] [Nonempty ι]
    [Field K] [CharZero K] (a : ι → K) (ha : ∀ i, a i ≠ 0) (L : ℕ)
    (hinj : ∀ i j, a i ^ L = a j ^ L → a i = a j) :
    ∃ t : ℕ, t < Fintype.card ι ∧ ComplexCSP.powerSum a (1 + L * t) ≠ 0 := by
  classical
  let S : Finset K := Finset.univ.image a
  let c : S → K := fun x ↦ ((Finset.univ.filter (fun i ↦ a i = x.val)).card : K) * x.val
  let b : S → K := fun x ↦ x.val ^ L
  have hb : Function.Injective b := by
    intro x y hxy
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp y.property
    apply Subtype.ext
    apply hi ▸ hj ▸ hinj i j
    simpa only [b, hi, hj] using hxy
  let i : ι := Classical.choice inferInstance
  let x : S := ⟨a i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩
  have hc : c x ≠ 0 := by
    apply mul_ne_zero
    · apply Nat.cast_ne_zero.mpr
      apply ne_of_gt
      apply Finset.card_pos.mpr
      exact ⟨i, by simp [x]⟩
    · exact ha i
  obtain ⟨t, ht, hsum⟩ := ComplexCSP.exists_weightedPowerSum_ne_zero_fintype c b hb ⟨x, hc⟩
  have hcard : Fintype.card S ≤ Fintype.card ι := by
    simpa only [Fintype.card_coe, S, Finset.card_univ] using Finset.card_image_le
      (s := Finset.univ) (f := a)
  refine ⟨t, lt_of_lt_of_le ht hcard, ?_⟩
  have heq : ComplexCSP.weightedPowerSum c b t = ComplexCSP.powerSum a (1 + L * t) := by
    change (∑ x : S, ((Finset.univ.filter (fun i ↦ a i = x.val)).card : K) * x.val *
      (x.val ^ L) ^ t) = _
    rw [Finset.sum_coe_sort S (fun x ↦
      ((Finset.univ.filter (fun i ↦ a i = x)).card : K) * x * (x ^ L) ^ t)]
    calc
      _ = ∑ i, a i * (a i ^ L) ^ t := by
        apply Finset.sum_image'
        intro j hj
        have heq : (∑ i ∈ Finset.univ.filter (fun i ↦ a i = a j),
            a i * (a i ^ L) ^ t) =
            ∑ _i ∈ Finset.univ.filter (fun i ↦ a i = a j), a j * (a j ^ L) ^ t := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [(Finset.mem_filter.mp hi).2]
        rw [heq]
        simp [nsmul_eq_mul, mul_assoc]
      _ = ComplexCSP.powerSum a (1 + L * t) := by
        simp only [ComplexCSP.powerSum, pow_add, pow_one, pow_mul]
  exact heq ▸ hsum

/-- Finite simultaneous nonvanishing on the required congruence class. If the
input values lie in a field whose roots of unity are killed by `E`, a witness
`t` exists below the product of the multiset sizes. This replaces the
finite-exception/SML argument for the row-detector search. -/
theorem exists_simultaneous_detector_time {ι K : Type*}
    [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)] [Field K] [CharZero K]
    (u : ∀ i, κ i → K) (hu : ∀ i j, u i j ≠ 0)
    (E L : ℕ) (hE : 0 < E) (hL : 0 < L) (hkill : KillsTorsion K E) :
    ∃ t : ℕ, t < ∏ i, Fintype.card (κ i) ∧
      ∀ i, ComplexCSP.powerSum (fun j ↦ u i j ^ E) (1 + L * t) ≠ 0 := by
  classical
  let a : (∀ i, κ i) → K := fun x ↦ ∏ i, u i (x i) ^ E
  have ha (x : ∀ i, κ i) : a x ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ ↦ pow_ne_zero E (hu i (x i)))
  have hinj (x y : ∀ i, κ i) (hxy : a x ^ L = a y ^ L) : a x = a y := by
    dsimp only [a] at hxy ⊢
    rw [Finset.prod_pow] at hxy ⊢
    rw [Finset.prod_pow] at hxy ⊢
    exact pow_injective_on_torsion_killing_powers E L hE hL hkill _ _
      (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hu i (x i)))
      (Finset.prod_ne_zero_iff.mpr (fun i _ ↦ hu i (y i))) hxy
  obtain ⟨t, ht, hnonzero⟩ := exists_powerSum_one_add_mul a ha L hinj
  change ComplexCSP.powerSum (fun x : ∀ i, κ i ↦ ∏ i, u i (x i) ^ E)
    (1 + L * t) ≠ 0 at hnonzero
  rw [← ComplexCSP.prod_powerSum_eq (fun i j ↦ u i j ^ E) (1 + L * t)] at hnonzero
  refine ⟨t, ?_, fun i ↦ Finset.prod_ne_zero_iff.mp hnonzero i (Finset.mem_univ i)⟩
  simpa only [Fintype.card_pi] using ht

/-- The same result with the paper's expanded entrywise exponent. -/
theorem exists_simultaneous_detector_exponent {ι K : Type*}
    [Fintype ι] [DecidableEq ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)] [Field K] [CharZero K]
    (u : ∀ i, κ i → K) (hu : ∀ i j, u i j ≠ 0)
    (E L : ℕ) (hE : 0 < E) (hL : 0 < L) (hkill : KillsTorsion K E) :
    ∃ t : ℕ, t < ∏ i, Fintype.card (κ i) ∧
      ∀ i, (∑ j, u i j ^ (E * (1 + t * L))) ≠ 0 := by
  simpa only [ComplexCSP.powerSum, pow_mul, Nat.mul_comm _ L] using
    exists_simultaneous_detector_time u hu E L hE hL hkill

/-- Exhaustive bounded search for the parameter `t` of the row detector.
This needs only field arithmetic and the supplied exact equality decision. -/
def findDetectorTime {ι K : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [Field K] [DecidableEq K]
    (u : ∀ i, κ i → K) (E L : ℕ) : Option ℕ :=
  (List.range (∏ i, Fintype.card (κ i))).find? (fun t ↦
    decide (∀ i, ComplexCSP.powerSum (fun j ↦ u i j ^ E) (1 + L * t) ≠ 0))

theorem findDetectorTime_sound {ι K : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [Field K] [DecidableEq K]
    (u : ∀ i, κ i → K) (E L : ℕ) {t : ℕ} (h : findDetectorTime u E L = some t) :
    t < ∏ i, Fintype.card (κ i) ∧
      ∀ i, ComplexCSP.powerSum (fun j ↦ u i j ^ E) (1 + L * t) ≠ 0 := by
  constructor
  · simpa only [List.mem_range] using List.mem_of_find?_eq_some h
  · simpa only [decide_eq_true_eq] using List.find?_some h

theorem findDetectorTime_success {ι K : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] [∀ i, Nonempty (κ i)]
    [Field K] [CharZero K] [DecidableEq K]
    (u : ∀ i, κ i → K) (hu : ∀ i j, u i j ≠ 0)
    (E L : ℕ) (hE : 0 < E) (hL : 0 < L) (hkill : KillsTorsion K E) :
    (findDetectorTime u E L).isSome = true := by
  obtain ⟨t, ht, hgood⟩ := exists_simultaneous_detector_time u hu E L hE hL hkill
  apply List.find?_isSome.mpr
  exact ⟨t, List.mem_range.mpr ht, by simp [hgood]⟩

/-- The row-detector expression before any support classification. -/
def detector {D K : Type*} [Fintype D] [CommSemiring K]
    (u v : D → K) (E q : ℕ) : K := ∑ z, u z ^ ((E - 1) * q) * v z ^ q

/-- Coordinate-level algebra for a row written as one scalar times phases times
another row. The hypothesis `1 ≤ E` handles the natural-number subtraction. -/
theorem detector_term_factor {K : Type*} [CommSemiring K]
    (u lam ζ : K) (E q : ℕ) (hE : 1 ≤ E) :
    u ^ ((E - 1) * q) * (lam * ζ * u) ^ q =
      lam ^ q * ζ ^ q * (u ^ E) ^ q := by
  have hexp : (E - 1) * q + q = E * q := by
    calc
      _ = (E - 1 + 1) * q := by ring
      _ = E * q := by rw [Nat.sub_add_cancel hE]
  calc
    _ = (lam ^ q * ζ ^ q) * (u ^ ((E - 1) * q) * u ^ q) := by
      simp only [mul_pow]
      ring
    _ = lam ^ q * ζ ^ q * (u ^ E) ^ q := by rw [← pow_add, hexp, pow_mul]

/-- The congruence class fixes every phase whose `L`th power is one. -/
theorem phase_pow_one_add_mul {K : Type*} [Monoid K]
    (ζ : K) (L t : ℕ) (hζ : ζ ^ L = 1) : ζ ^ (1 + L * t) = ζ := by
  rw [pow_add, pow_one, pow_mul, hζ, one_pow, mul_one]

/-- One purified block remains zero for every allowed detector exponent. The
hypothesis concerns constant `E`th powers on the block, not equality of ordinary
complex absolute values. -/
theorem detector_block_eq_zero {D K : Type*} [CommRing K]
    (u v ζ : D → K) (B : Finset D) (lam c : K) (E L t : ℕ) (hE : 1 ≤ E)
    (hrow : ∀ z ∈ B, v z = lam * ζ z * u z)
    (hphase : ∀ z ∈ B, ζ z ^ L = 1)
    (hconst : ∀ z ∈ B, u z ^ E = c) (hsum : ∑ z ∈ B, ζ z = 0) :
    (∑ z ∈ B, u z ^ ((E - 1) * (1 + L * t)) * v z ^ (1 + L * t)) = 0 := by
  calc
    _ = ∑ z ∈ B, (lam ^ (1 + L * t) * c ^ (1 + L * t)) * ζ z := by
      apply Finset.sum_congr rfl
      intro z hz
      rw [hrow z hz, detector_term_factor _ _ _ _ _ hE,
        phase_pow_one_add_mul _ _ _ (hphase z hz), hconst z hz]
      ring
    _ = 0 := by rw [← Finset.mul_sum, hsum, mul_zero]

/-- The zero side of row detection after the common support is partitioned by a
finite block-label function. Fibers enforce coverage and disjointness by
construction. The required constant-power and phase-sum properties are the
purified-block algebraic invariants. -/
theorem detector_eq_zero_of_blocks {D J K : Type*}
    [Fintype D] [Fintype J] [DecidableEq J] [CommRing K]
    (u v ζ : D → K) (S : Finset D) (block : D → J) (c : J → K)
    (lam : K) (E L t : ℕ) (hE : 1 ≤ E)
    (houtside : ∀ z, z ∉ S → v z = 0)
    (hrow : ∀ z ∈ S, v z = lam * ζ z * u z)
    (hphase : ∀ z ∈ S, ζ z ^ L = 1)
    (hconst : ∀ z ∈ S, u z ^ E = c (block z))
    (hsum : ∀ j, (∑ z ∈ S.filter (fun z ↦ block z = j), ζ z) = 0) :
    detector u v E (1 + L * t) = 0 := by
  classical
  have hrestrict : detector u v E (1 + L * t) =
      ∑ z ∈ S, u z ^ ((E - 1) * (1 + L * t)) * v z ^ (1 + L * t) := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z _ hz
    rw [houtside z hz, zero_pow (by omega), mul_zero]
  rw [hrestrict, ← Finset.sum_fiberwise S block]
  apply Finset.sum_eq_zero
  intro j _
  apply detector_block_eq_zero u v ζ _ lam (c j) E L t hE
  · intro z hz
    exact hrow z (Finset.mem_filter.mp hz).1
  · intro z hz
    exact hphase z (Finset.mem_filter.mp hz).1
  · intro z hz
    rw [hconst z (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2]
  · exact hsum j

/-- The dependent-row side of the detector factors into a nonzero scalar power
and the pure power sum addressed by the finite simultaneous search. -/
theorem detector_eq_scalar_mul_powerSum {D K : Type*} [Fintype D] [CommSemiring K]
    (u v : D → K) (lam : K) (E q : ℕ) (hE : 1 ≤ E)
    (hrow : ∀ z, v z = lam * u z) :
    detector u v E q = lam ^ q * ComplexCSP.powerSum (fun z ↦ u z ^ E) q := by
  unfold detector ComplexCSP.powerSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  rw [hrow z]
  simpa only [mul_one, one_pow] using detector_term_factor (u z) lam 1 E q hE

theorem detector_ne_zero_of_dependent {D K : Type*} [Fintype D]
    [CommRing K] [IsDomain K] (u v : D → K) (lam : K) (hlam : lam ≠ 0)
    (E q : ℕ) (hE : 1 ≤ E) (hrow : ∀ z, v z = lam * u z)
    (hsum : ComplexCSP.powerSum (fun z ↦ u z ^ E) q ≠ 0) :
    detector u v E q ≠ 0 := by
  rw [detector_eq_scalar_mul_powerSum u v lam E q hE hrow]
  exact mul_ne_zero (pow_ne_zero q hlam) hsum

end ComplexCSP.RowDetector
