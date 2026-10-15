import ComplexCSP.Recognition.GlobalConditions
import ComplexCSP.Algebra.LegalPurificationTables
import ComplexCSP.Structure.BlockRowPhases
import ComplexCSP.Algebra.NumberFieldTorsion
import ComplexCSP.Recognition.GeneratedDetector
import ComplexCSP.Algebra.WorkingField

/-!
# Actual row-equivalence detector

This file connects legal purified magnitude blocks, original row phases,
number-field torsion, finite simultaneous nonvanishing and the literal generated
detector. Auxiliary algebraic lemmas do not assume the desired support equality.
-/
namespace ComplexCSP.RowEquivalenceRealization

open BlockOrthogonality RowTypes RowPhases RowDetector
open Purification PurificationMap
open scoped BigOperators

universe u v

/-- A norm equality within a purified block forces an original torsion ratio. -/
theorem source_ratio_finite_order {Γ : Type u} [CommGroup Γ] {original : Γ →* ℂˣ}
    (P : PurificationMap Γ original) (a b : Option Γ)
    (hb : P.source b ≠ 0) (h : ‖P.entry a‖ = ‖P.entry b‖) :
    IsOfFinOrder (P.source a / P.source b) := by
  cases a with
  | none =>
    have hz : P.entry b = 0 := norm_eq_zero.mp (by simpa using h.symm)
    exact False.elim (hb ((P.source_eq_zero_iff b).mpr ((P.entry_eq_zero_iff b).mp hz)))
  | some a =>
    cases b with
    | none => exact False.elim (hb rfl)
    | some b =>
      have ht := ((Units.coeHom ℂ).comp original).isOfFinOrder
        ((P.norm_eq_iff_torsion a b).mp h)
      simpa [map_div] using ht

/-- A zero Hermitian block sum with constant nonzero row magnitude forces the
sum of its relative phases to vanish. -/
theorem phase_sum_zero {D : Type u} (u v ζ : D → ℂ) (B : Finset D)
    (z₀ : D) (lam : ℂ) (hu : u z₀ ≠ 0) (hlam : lam ≠ 0)
    (hrow : ∀ z ∈ B, v z = lam * ζ z * u z)
    (hnorm : ∀ z ∈ B, ‖u z‖ = ‖u z₀‖)
    (hsum : hermitianSum u v B = 0) : (∑ z ∈ B, ζ z) = 0 := by
  have hnormprod : ∀ z ∈ B, u z * star (u z) = u z₀ * star (u z₀) := by
    intro z hz
    change u z * (starRingEnd ℂ) (u z) = u z₀ * (starRingEnd ℂ) (u z₀)
    rw [Complex.mul_conj', Complex.mul_conj', hnorm z hz]
  have heq : hermitianSum u v B =
      (star lam * (u z₀ * star (u z₀))) * star (∑ z ∈ B, ζ z) := by
    rw [star_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    rw [hrow z hz]
    simp only [star_mul]
    calc
      u z * (star (u z) * (star (ζ z) * star lam)) =
        (star lam * (u z * star (u z))) * star (ζ z) := by ring
      _ = _ := by rw [hnormprod z hz]
  have hfactor : star lam * (u z₀ * star (u z₀)) ≠ 0 := by
    exact mul_ne_zero (by simpa using hlam) (mul_ne_zero hu (by simpa using hu))
  rw [heq] at hsum
  exact star_eq_zero.mp ((mul_eq_zero.mp hsum).resolve_left hfactor)

/-- A field's root exponent kills every complex finite-order element lying in
that field, by lifting to the actual field subtype. -/
theorem field_torsion_power (K : Subfield ℂ) [NumberField K]
    {z : ℂ} (hz : z ∈ K) (ht : IsOfFinOrder z) : z ^ fieldExponent K = 1 := by
  let x : K := ⟨z, hz⟩
  have hx : IsOfFinOrder x := K.subtype.injective.isOfFinOrder_iff.mp ht
  exact congrArg Subtype.val (fieldExponent_killsTorsion K x hx)

theorem purifiedTable_eq_zero_iff {X : Type u} {D : Type v}
    (G : X → D → ℂ) (P : PurificationMap (entryGroup G) (entryGroup G).subtype)
    (x : X) (z : D) : PurificationMap.purifyTable G P x z = 0 ↔ G x z = 0 := by
  classical
  by_cases h : G x z = 0 <;>
    simp [PurificationMap.purifyTable, encodeTable, h]

/-- Independent overlapping rows contribute zero to every permitted detector
exponent. All block invariants are derived from legal purification structure. -/
theorem independent_detector_zero {X : Type u} {D : Type v} [Fintype D]
    (G : X → D → ℂ) (P : PurificationMap (entryGroup G) (entryGroup G).subtype)
    (hP : BlockOrthogonal (PurificationMap.purifyTable G P))
    (hpow : ∀ h, 0 < h → h ≤ Fintype.card D → BlockOrthogonal (fun x z => G x z ^ h))
    (K : Subfield ℂ) [NumberField K] (hK : ∀ x z, G x z ∈ K)
    (x y : X) (z₀ : D) (hx : G x z₀ ≠ 0) (hy : G y z₀ ≠ 0)
    (hind : ¬ Proportional (G x) (G y)) (t : ℕ) :
    detector (G x) (G y) (fieldExponent K)
      (1 + phaseExponent (Fintype.card D) * t) = 0 := by
  classical
  let U := PurificationMap.purifyTable G P
  let L := phaseExponent (Fintype.card D)
  let E := fieldExponent K
  let lam := anchorScalar (G x) (G y) z₀
  let ζ := anchoredPhase (G x) (G y) z₀
  obtain ⟨hsupport, hlam, _, hphase⟩ := finite_row_phases_of_power_BO G hpow x y z₀ hx hy
  have hxP : U x z₀ ≠ 0 := (not_congr (purifiedTable_eq_zero_iff G P x z₀)).mpr hx
  have hyP : U y z₀ ≠ 0 := (not_congr (purifiedTable_eq_zero_iff G P y z₀)).mpr hy
  have hmag := magnitudeProportional_of_overlap hP.1 x y z₀ hxP hyP
  have hxrow : U x ≠ 0 := by intro he; exact hxP (congrFun he z₀)
  have hyrow : U y ≠ 0 := by intro he; exact hyP (congrFun he z₀)
  have horth : VectorBlockOrthogonal (U x) (U y) := by
    rcases hP.2 x y hxrow hyrow hmag with hdep | ho
    · exfalso
      apply hind
      have hh := P.source_proportional_of (encodeTable G x) (encodeTable G y) hxrow hyrow hdep
      simp only [Function.comp_def, source_encodeTable] at hh
      exact hh
    · exact ho
  let S : Finset D := Finset.univ.filter fun z => G x z ≠ 0
  let f : D → ℝ := fun z => ‖U x z‖
  let g : D → ℂ := fun z => G x z ^ ((E - 1) * (1 + L * t)) * G y z ^ (1 + L * t)
  have hE : 2 ≤ E := fieldExponent_ge_two K
  have hrestrict : detector (G x) (G y) E (1 + L * t) = ∑ z ∈ S, g z := by
    symm
    apply Finset.sum_subset (Finset.subset_univ S)
    intro z _ hz
    have hu : G x z = 0 := by simpa [S] using hz
    have hexp : (E - 1) * (1 + L * t) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    change g z = 0
    simp only [g, hu, zero_pow hexp, zero_mul]
  rw [hrestrict, ← Finset.sum_fiberwise_of_maps_to (s := S) (t := S.image f)
    (g := f) (fun z hz => Finset.mem_image_of_mem f hz) g]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hr
  have hwG : G x w ≠ 0 := (Finset.mem_filter.mp hw).2
  have hwP : U x w ≠ 0 := (not_congr (purifiedTable_eq_zero_iff G P x w)).mpr hwG
  have hfilter : S.filter (fun z => f z = f w) = BlockOrthogonality.magnitudeBlock (U x) w := by
    ext z
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨_, hz⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    · intro hz
      have hnorm := (Finset.mem_filter.mp hz).2
      have hzP : U x z ≠ 0 := by
        intro hzero
        have hwzero : ‖U x w‖ = 0 := by simpa [hzero] using hnorm.symm
        exact hwP (norm_eq_zero.mp hwzero)
      exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (not_congr (purifiedTable_eq_zero_iff G P x z)).mp hzP⟩, hnorm⟩
  rw [hfilter]
  let B := BlockOrthogonality.magnitudeBlock (U x) w
  have hBnonzero : ∀ z ∈ B, G x z ≠ 0 := by
    intro z hz
    have hmem : z ∈ S.filter (fun z => f z = f w) := hfilter.symm ▸ hz
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hmem).1).2
  have hnormP : ∀ z ∈ B, ‖U x z‖ = ‖U x w‖ := fun z hz => (Finset.mem_filter.mp hz).2
  have hnormG : ∀ z ∈ B, ‖G x z‖ = ‖G x w‖ := by
    intro z hz
    have hn := P.source_norm_eq_of (hnormP z hz)
    simpa only [source_encodeTable] using hn
  have hsum : hermitianSum (G x) (G y) B = 0 := by
    have hh := P.source_sum_on_purified_block (encodeTable G x) (encodeTable G y) hmag horth w hwP
    simp only [Function.comp_def, source_encodeTable] at hh
    exact hh
  apply detector_block_eq_zero (G x) (G y) ζ B lam (G x w ^ E) E L t (by omega)
  · intro z hz
    exact (hphase z (hBnonzero z hz)).1
  · intro z hz
    exact (hphase z (hBnonzero z hz)).2.2
  · intro z hz
    have ht : IsOfFinOrder (G x z / G x w) := by
      have hh := source_ratio_finite_order P (encodeTable G x z) (encodeTable G x w)
        (by simpa only [source_encodeTable] using hwG) (hnormP z hz)
      simpa only [source_encodeTable] using hh
    have hp := field_torsion_power K (K.div_mem (hK x z) (hK x w)) ht
    rw [div_pow] at hp
    exact (div_eq_one_iff_eq (pow_ne_zero E hwG)).mp hp
  · exact phase_sum_zero (G x) (G y) ζ B w lam hwG hlam
      (fun z hz => (hphase z (hBnonzero z hz)).1) hnormG hsum

/-- One bounded finite simultaneous search makes the pure power sum nonzero on
every nonzero row. The field and its torsion exponent are actual number-field data. -/
theorem exists_nonzero_row_sums {X : Type u} {D : Type v} [Fintype X] [Fintype D]
    (G : X → D → ℂ) (K : Subfield ℂ) [NumberField K]
    (hK : ∀ x z, G x z ∈ K) (L : ℕ) (hL : 0 < L) :
    ∃ t : ℕ, ∀ x, G x ≠ 0 →
      powerSum (fun z => G x z ^ fieldExponent K) (1 + L * t) ≠ 0 := by
  classical
  let R := {x : X // G x ≠ 0}
  let Z : R → Type v := fun x => {z : D // G x.val z ≠ 0}
  letI : ∀ x : R, Nonempty (Z x) := fun x => by
    have h : ∃ z, G x.val z ≠ 0 := by
      by_contra! hz
      exact x.property (funext hz)
    obtain ⟨z, hz⟩ := h
    exact ⟨⟨z, hz⟩⟩
  let u : ∀ x : R, Z x → K := fun x z => ⟨G x.val z.val, hK _ _⟩
  have hu : ∀ x z, u x z ≠ 0 := by
    intro x z hz
    exact z.property (congrArg Subtype.val hz)
  obtain ⟨t, _, ht⟩ := numberField_exists_simultaneous_detector_time u hu L hL
  refine ⟨t, ?_⟩
  intro x hx
  let xr : R := ⟨x, hx⟩
  have hmap : (∑ z : Z xr, (G x z.val ^ fieldExponent K) ^ (1 + L * t)) ≠ 0 := by
    have hnonzero : K.subtype (powerSum (fun z => u xr z ^ fieldExponent K) (1 + L * t)) ≠ 0 := by
      intro hz
      exact ht xr (K.subtype.injective (by simpa using hz))
    simpa only [powerSum, map_sum, map_pow, Subfield.subtype_apply, u] using hnonzero
  have heq : powerSum (fun z => G x z ^ fieldExponent K) (1 + L * t) =
      ∑ z : Z xr, (G x z.val ^ fieldExponent K) ^ (1 + L * t) := by
    let S := Finset.univ.filter fun z => G x z ≠ 0
    calc
      _ = ∑ z ∈ S, (G x z ^ fieldExponent K) ^ (1 + L * t) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ S)
        intro z _ hz
        have hzG : G x z = 0 := by simpa [S] using hz
        rw [hzG, zero_pow (ne_of_gt (fieldExponent_pos K)), zero_pow (by omega)]
      _ = _ := Finset.sum_subtype S (fun z => by simp [S, xr]) _
  exact heq ▸ hmap

/-- The detector support is exactly the nonzero proportional-row relation,
with no support classification supplied as a hypothesis. -/
theorem exists_detector_support {X : Type u} {D : Type v} [Fintype X] [Fintype D]
    (G : X → D → ℂ) (P : PurificationMap (entryGroup G) (entryGroup G).subtype)
    (hP : BlockOrthogonal (PurificationMap.purifyTable G P))
    (hpow : ∀ h, 0 < h → h ≤ Fintype.card D → BlockOrthogonal (fun x z => G x z ^ h))
    (K : Subfield ℂ) [NumberField K] (hK : ∀ x z, G x z ∈ K) :
    ∃ t : ℕ, ∀ x y,
      detector (G x) (G y) (fieldExponent K) (1 + phaseExponent (Fintype.card D) * t) ≠ 0 ↔
        NonzeroProportionalRows G x y := by
  obtain ⟨t, ht⟩ := exists_nonzero_row_sums G K hK _ (phaseExponent_pos _)
  refine ⟨t, ?_⟩
  intro x y
  constructor
  · intro hnonzero
    by_contra hnot
    apply hnonzero
    by_cases hmeet : ∃ z, G x z ≠ 0 ∧ G y z ≠ 0
    · obtain ⟨z, hxz, hyz⟩ := hmeet
      have hx : G x ≠ 0 := by intro he; exact hxz (congrFun he z)
      have hy : G y ≠ 0 := by intro he; exact hyz (congrFun he z)
      have hind : ¬ Proportional (G x) (G y) := fun hp => hnot ⟨hx, hy, hp⟩
      exact independent_detector_zero G P hP hpow K hK x y z hxz hyz hind t
    · apply Finset.sum_eq_zero
      intro z _
      have he : G x z = 0 ∨ G y z = 0 := by
        by_contra! hz
        exact hmeet ⟨z, hz⟩
      rcases he with he | he
      · have hexp : (fieldExponent K - 1) * (1 + phaseExponent (Fintype.card D) * t) ≠ 0 :=
          Nat.mul_ne_zero (by have := fieldExponent_ge_two K; omega) (by omega)
        rw [he, zero_pow hexp, zero_mul]
      · rw [he, zero_pow (by omega), mul_zero]
  · rintro ⟨hx, hy, hprop⟩
    obtain ⟨lam, hlam, hrow⟩ := proportional_symm hprop
    exact detector_ne_zero_of_dependent (G x) (G y) lam hlam _ _
      (by have := fieldExponent_ge_two K; omega) hrow (ht x hx)

/-! ## Instantiation by the actual language, generated tables and joint BO -/

/-- Theorem 8.4's concrete detector is generated and realizes the literal
row-equivalence relation. The number field and its torsion exponent are derived
from algebraicity of the finite input language. -/
theorem generated_row_equivalence_detector {D ι : Type} [Fintype D] [Fintype ι]
    (L : Language D ℂ ι) (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a))
    (hBO : JointBO L) {n : ℕ} (hn : 0 < n)
    (G : (Fin (n + 1) → D) → ℂ) (hG : Instance.Generated L G) :
    ∃ E t : ℕ, 2 ≤ E ∧
      Instance.Generated L (rowDetector G
        ((E - 1) * (1 + phaseExponent (Fintype.card D) * t))
        (1 + phaseExponent (Fintype.card D) * t)) ∧
      ∀ a : Fin (n + n) → D,
        rowDetector G ((E - 1) * (1 + phaseExponent (Fintype.card D) * t))
            (1 + phaseExponent (Fintype.card D) * t) a ≠ 0 ↔
          a ∈ (omegaRelation G).tuples := by
  classical
  let T : PositiveTable D := ⟨n, G⟩
  let C := GeneratingSet.LegalGeneratingSet.choose T.nonzeroValues
  have hcontains : GeneratingSet.LegalGeneratingSet.ContainsTable T.nonzeroValues (tableRows G) := by
    intro x z hz
    exact (T.mem_nonzeroValues _).mpr ⟨x, z, rfl⟩
  let P := C.tableMap (tableRows G) hcontains
  have hP : BlockOrthogonal (PurificationMap.purifyTable (tableRows G) P) := by
    exact (jointBO_iff_singletonBO L).mp hBO T hG hn
  have hpow : ∀ h, 0 < h → h ≤ Fintype.card D →
      BlockOrthogonal (fun x z => tableRows G x z ^ h) := by
    intro h _ _
    exact hBO.original L n (fun a => G a ^ h) (Instance.generated_pow hG h)
  let K : Subfield ℂ := L.workingField.toSubfield
  letI : NumberField K := L.workingField_numberField hAlg
  have hK : ∀ x z, tableRows G x z ∈ K := by
    intro x z
    exact Instance.generated_mem_workingField hG (Fin.snoc x z)
  obtain ⟨t, ht⟩ := exists_detector_support (tableRows G) P hP hpow K hK
  refine ⟨fieldExponent K, t, fieldExponent_ge_two K, generated_rowDetector hG _ _, ?_⟩
  intro a
  exact ht (fun i => a (Fin.castAdd n i)) (fun i => a (Fin.natAdd n i))

/-- The exact Ω relation is a support of an actual generated table. -/
theorem omega_mem_generatedSupports {D ι : Type} [Fintype D] [Fintype ι]
    (L : Language D ℂ ι) (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a))
    (hBO : JointBO L) {n : ℕ} (hn : 0 < n)
    (G : (Fin (n + 1) → D) → ℂ) (hG : Instance.Generated L G) :
    omegaRelation G ∈ generatedSupports L := by
  obtain ⟨E, t, _, hdet, hsupp⟩ := generated_row_equivalence_detector L hAlg hBO hn G hG
  refine ⟨rowDetector G ((E - 1) * (1 + phaseExponent (Fintype.card D) * t))
      (1 + phaseExponent (Fintype.card D) * t), hdet, ?_⟩
  ext a
  exact (hsupp a).symm

/-- One operation simultaneously preserves every actual generated support and
every applicable original-table Ω relation. This is the common operation
required in the structural conclusion, not a separate operation per table. -/
theorem common_support_and_row_maltsev {D ι : Type} [Fintype D] [Nonempty D] [Fintype ι]
    (L : Language D ℂ ι) (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) (hBO : JointBO L) :
    ∃ m : MaltsevRelations.Operation D, MaltsevRelations.IsMaltsev m ∧
      MaltsevRelations.CommonPolymorphism (generatedSupports L) m ∧
      ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n + 1) → D) → ℂ),
        Instance.Generated L G → MaltsevRelations.Preserves m (omegaRelation G).tuples := by
  obtain ⟨m, hm, hsupp⟩ := hBO.common_support_maltsev L
  exact ⟨m, hm, hsupp, fun n hn G hG =>
    hsupp (omegaRelation G) (omega_mem_generatedSupports L hAlg hBO hn G hG)⟩

/-- The Type Partition half of the structural collapse for every original
generated complex table and every actual prefix length. -/
theorem generated_type_partition {D ι : Type} [Fintype D] [Nonempty D] [Fintype ι]
    (L : Language D ℂ ι) (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) (hBO : JointBO L)
    {n : ℕ} (hn : 0 < n) (G : (Fin (n + 1) → D) → ℂ) (hG : Instance.Generated L G)
    {ℓ : ℕ} (hℓ : ℓ ≤ n) (α β : Fin ℓ → D) :
    prefixType G hℓ α = prefixType G hℓ β ∨
      Disjoint (prefixType G hℓ α) (prefixType G hℓ β) := by
  obtain ⟨m, hm, _, hrow⟩ := common_support_and_row_maltsev L hAlg hBO
  exact complex_type_partition G hm (hrow n hn G hG) hℓ α β

end ComplexCSP.RowEquivalenceRealization
