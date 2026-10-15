import ComplexCSP.Structure.WeightedMaltsevLayer
import ComplexCSP.Structure.MaltsevTypeAlgebra
import ComplexCSP.Structure.BlockOrthogonalRowCount

/-! # Actual row equivalence supplies every structural layer hypothesis -/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness
variable {K : Type} [Field K] [DecidableEq K] {d n : ℕ}

theorem tableLabel_eq_iff (G : (Fin (n + 1) → Fin d) → K) (x y : Fin n → Fin d)
    (hx : x ∈ rowSupport G) :
    tableLabel G x = tableLabel G y ↔ RowTypes.Proportional (tableRows G x) (tableRows G y) := by
  constructor
  · intro he
    have hd := congrArg decodeLabel he
    simp only [tableLabel, normalizedRow, view_ofFn, decode_materialize] at hd
    exact (ComplexityRowNormalization.normalize_eq_iff _ _ hx).mp hd
  · intro hp
    have he := (ComplexityRowNormalization.normalize_eq_iff _ _ hx).mpr hp
    simpa only [tableLabel, normalizedRow, view_ofFn] using congrArg materializeLabel he

theorem rowFiber_equivalence (G : (Fin (n + 1) → Fin d) → K) (x y : Fin n → Fin d) :
    RowEquivalence (rowFiber G) x y ↔ RowTypes.NonzeroProportionalRows (tableRows G) x y := by
  constructor
  · rintro ⟨L, ⟨hx, hxl⟩, ⟨hy, hyl⟩⟩
    exact ⟨hx, hy, (tableLabel_eq_iff G x y hx).mp (hxl.trans hyl.symm)⟩
  · rintro ⟨hx, hy, hp⟩
    exact ⟨tableLabel G x, ⟨hx, rfl⟩, hy, ((tableLabel_eq_iff G x y hx).mpr hp).symm⟩

theorem rowFiber_equivalence_complex (G : (Fin (n + 1) → Fin d) → K) (σ : K →+* ℂ)
    (x y : Fin n → Fin d) :
    RowEquivalence (rowFiber G) x y ↔ RowTypes.Omega (fun a => σ (G a)) x y := by
  classical
  rw [rowFiber_equivalence]
  change (tableRows G x ≠ 0 ∧ tableRows G y ≠ 0 ∧ RowTypes.Proportional (tableRows G x) (tableRows G y)) ↔
    ((fun z => σ (tableRows G x z)) ≠ 0 ∧ (fun z => σ (tableRows G y z)) ≠ 0 ∧
      RowTypes.Proportional (fun z => σ (tableRows G x z)) (fun z => σ (tableRows G y z)))
  rw [← RowTypes.nonzeroProportionalTest_correct, ← RowTypes.nonzeroProportionalTest_correct,
    RowTypes.nonzeroProportionalTest_map]

theorem labelFiber_rowFiber (G : (Fin (n + 1) → Fin d) → K) :
    labelFiber (rowSupport G) (fun x => tableLabel G (view x)) = rowFiber G := by
  funext a
  ext x
  simp only [labelFiber, rowFiber, Set.mem_setOf_eq, view_ofFn]

/-- The complex Ω relation is transported back to the executable field labels. -/
theorem row_equivalence_of_omega (G : (Fin (n + 1) → Fin d) → K) (σ : K →+* ℂ)
    {m : Operation (Fin d)} (h : Preserves m (RowTypes.omegaRelation (fun a => σ (G a))).tuples) :
    PreservesRowEquivalence m (rowFiber G) := by
  intro x₁ x₂ y₁ y₂ z₁ z₂ hx hy hz
  apply (rowFiber_equivalence_complex G σ _ _).mpr
  exact RowTypes.preserves_omega_pairs (fun a => σ (G a)) h _ _ _ _ _ _
    ((rowFiber_equivalence_complex G σ _ _).mp hx)
    ((rowFiber_equivalence_complex G σ _ _).mp hy)
    ((rowFiber_equivalence_complex G σ _ _).mp hz)

theorem omega_supplies_layer_hypotheses (G : (Fin (n + 1) → Fin d) → K) (σ : K →+* ℂ)
    {m : Operation (Fin d)} (hm : IsMaltsev m)
    (h : Preserves m (RowTypes.omegaRelation (fun a => σ (G a))).tuples) :
    Preserves m (rowSupport G) ∧
    AllTypesPartition (rowSupport G) (fun x => tableLabel G (view x)) ∧
    ∀ a, Preserves m (rowFiber G a) := by
  have hr := row_equivalence_of_omega G σ h
  rw [← labelFiber_rowFiber G] at hr
  refine ⟨row_equivalence_support_preserves hr, allTypesPartition_of_row_equivalence hm hr, ?_⟩
  intro a
  simpa only [labelFiber_rowFiber] using row_equivalence_fibers_preserves hm hr a

/-- At arity one there is a single row index, so no positive-arity Ω premise
is needed from the source's Mal'tsev condition. -/
theorem omega_zero_preserved (G : (Fin 1 → Fin d) → ℂ) (m : Operation (Fin d)) :
    Preserves m (RowTypes.omegaRelation G).tuples := by
  intro x hx y hy z hz
  have he : map₃ m x y z = x := by funext i; exact Fin.elim0 i
  rwa [he]

/-- Proof-side image bound for the actual materialized labels. -/
noncomputable def presentLabels (G : (Fin (n + 1) → Fin d) → K) : Finset (RowLabel K d) :=
  (BlockOrthogonalRowCount.normalizedLabels (tableRows G)).image materializeLabel

theorem tableLabel_mem_present (G : (Fin (n + 1) → Fin d) → K)
    (x : Fin n → Fin d) (hx : x ∈ rowSupport G) : tableLabel G x ∈ presentLabels G := by
  apply Finset.mem_image.mpr
  refine ⟨ComplexityRowNormalization.normalize (tableRows G x), ?_, by simp [tableLabel, normalizedRow]⟩
  apply (BlockOrthogonalRowCount.mem_normalizedLabels _ _).mpr
  exact ⟨fun h => hx ((ComplexityRowNormalization.normalize_none_iff _).mp h), x, rfl⟩

theorem presentLabels_card_le (G : (Fin (n + 1) → Fin d) → K) (σ : K →+* ℂ)
    (hBO : BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows G x a))) :
    (presentLabels G).card ≤ d :=
  (Finset.card_image_le).trans (BlockOrthogonalRowCount.normalizedLabels_card_le (tableRows G) σ hBO)

end ComplexCSP.WeightedMaltsev
