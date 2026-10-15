import ComplexCSP.Structure.BlockOrthogonality
import ComplexCSP.Complexity.RowNormalization
import ComplexCSP.Recognition.GeneratedDetectorAlgorithms
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # A proved finite bound on actual normalized row labels

Block Orthogonality gives ordinary pairwise Hermitian orthogonality between
nonproportional nonzero rows. Linear independence then bounds their number by
the number of columns. No finite row-class alphabet is assumed as input.
-/
namespace ComplexCSP.BlockOrthogonalRowCount
open scoped BigOperators
open BlockOrthogonality RowTypes

variable {D X : Type} [Fintype D]

theorem vectorBlockOrthogonal_sum {u v : D → ℂ} (h : VectorBlockOrthogonal u v) :
    (∑ z, u z * star (v z)) = 0 := by
  classical
  let T := Finset.univ.image (fun z => ‖u z‖)
  have hm : ∀ z ∈ (Finset.univ : Finset D), ‖u z‖ ∈ T := by
    intro z hz
    exact Finset.mem_image.mpr ⟨z,hz,rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hm (fun z => u z * star (v z))]
  apply Finset.sum_eq_zero
  intro r hr
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hr
  by_cases ha : u a = 0
  · apply Finset.sum_eq_zero
    intro z hz
    have he := (Finset.mem_filter.mp hz).2
    have hz0 : u z = 0 := norm_eq_zero.mp (by simpa [ha] using he)
    simp [hz0]
  · exact h a ha

theorem hermitian_zero_of_nonproportional {G : X → D → ℂ} (hBO : BlockOrthogonal G)
    (x y : X) (hx : G x ≠ 0) (hy : G y ≠ 0) (hp : ¬Proportional (G x) (G y)) :
    (∑ z, G x z * star (G y z)) = 0 := by
  classical
  rcases hBO.1 x y hx hy with hm | hd
  · rcases hBO.2 x y hx hy hm with hprop | ho
    · exact (hp hprop).elim
    · exact vectorBlockOrthogonal_sum ho
  · apply Finset.sum_eq_zero
    intro z _
    by_cases hxz : G x z = 0
    · simp [hxz]
    · have hyz : G y z = 0 := by
        by_contra hn
        exact Set.disjoint_left.mp hd hxz hn
      simp [hyz]

/-- Any finite list of inequivalent nonzero rows has at most one column's worth
of elements; this includes empty domains and arbitrary ambient index types. -/
theorem nonproportional_card_le {I : Type} [Fintype I] (G : I → D → ℂ)
    (hBO : BlockOrthogonal G) (hn : ∀ i, G i ≠ 0)
    (hp : Pairwise fun i j => ¬Proportional (G i) (G j)) :
    Fintype.card I ≤ Fintype.card D := by
  let v : I → EuclideanSpace ℂ D := fun i => WithLp.toLp 2 (G i)
  have hz : ∀ i, v i ≠ 0 := by
    intro i hi
    apply hn i
    funext z
    have he := congrArg (fun w : EuclideanSpace ℂ D => w z) hi
    exact he
  have ho : Pairwise fun i j => inner ℂ (v i) (v j) = 0 := by
    intro i j hij
    have he := hermitian_zero_of_nonproportional hBO j i (hn j) (hn i) (hp hij.symm)
    simpa [PiLp.inner_apply, RCLike.inner_apply, v, mul_comm] using he
  have hlin := linearIndependent_of_ne_zero_of_inner_eq_zero hz ho
  simpa only [finrank_euclideanSpace] using hlin.fintype_card_le_finrank

section NormalizedLabels
open ComplexityRowNormalization
variable {K : Type} [Field K] [DecidableEq K] {d : ℕ} [Fintype X]

/-- The actual finite image of present normalized rows, used only in proofs of
bounds. Algorithms build materialized lists and do not enumerate this finset. -/
noncomputable def normalizedLabels (G : X → Row K d) : Finset (Result K d) := by
  classical
  exact (Finset.univ.image (fun x => normalize (G x))).erase none

theorem mem_normalizedLabels (G : X → Row K d) (r : Result K d) :
    r ∈ normalizedLabels G ↔ r ≠ none ∧ ∃ x, normalize (G x) = r := by
  classical
  simp [normalizedLabels]

/-- The image bound applies in the actual working field through any embedding;
no larger supplied row-class alphabet is needed by the type-search algorithm. -/
theorem normalizedLabels_card_le (G : X → Row K d) (σ : K →+* ℂ)
    (hBO : BlockOrthogonal (fun x j => σ (G x j))) :
    (normalizedLabels G).card ≤ d := by
  classical
  let S := normalizedLabels G
  let pick : {r // r ∈ S} → X := fun r =>
    Classical.choose ((mem_normalizedLabels G r.val).mp r.property).2
  have he (r : {r // r ∈ S}) : normalize (G (pick r)) = r.val :=
    Classical.choose_spec ((mem_normalizedLabels G r.val).mp r.property).2
  have hn (r : {r // r ∈ S}) : G (pick r) ≠ 0 := by
    intro h
    have hz : normalize (G (pick r)) = none := (normalize_none_iff _).mpr h
    exact ((mem_normalizedLabels G r.val).mp r.property).1 ((he r).symm.trans hz)
  let rows : {r // r ∈ S} → Fin d → ℂ := fun r j => σ (G (pick r) j)
  have hrows (r : {r // r ∈ S}) : rows r ≠ 0 := by
    intro h
    apply hn r
    funext j
    apply σ.injective
    simpa [rows] using congrFun h j
  have hb : BlockOrthogonal rows := by
    constructor
    · intro r t hr ht
      exact hBO.1 (pick r) (pick t) hr ht
    · intro r t hr ht hm
      exact hBO.2 (pick r) (pick t) hr ht hm
  have hp : Pairwise fun r t => ¬Proportional (rows r) (rows t) := by
    intro r t hrt hprop
    have ht := (nonzeroProportionalTest_correct (rows r) (rows t)).mpr
      ⟨hrows r, hrows t, hprop⟩
    change nonzeroProportionalTest (fun j => σ (G (pick r) j))
      (fun j => σ (G (pick t) j)) = true at ht
    rw [nonzeroProportionalTest_map] at ht
    have hp' := (nonzeroProportionalTest_correct (G (pick r)) (G (pick t))).mp ht
    have heq := (normalize_eq_iff (G (pick r)) (G (pick t)) hp'.1).mpr hp'.2.2
    rw [he r,he t] at heq
    exact hrt (Subtype.ext heq)
  have hc := nonproportional_card_le rows hb hrows hp
  simpa only [Fintype.card_coe, Fintype.card_fin] using hc

end NormalizedLabels

end ComplexCSP.BlockOrthogonalRowCount
