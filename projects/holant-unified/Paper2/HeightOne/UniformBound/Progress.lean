import Paper2.HeightOne.UniformBound.Main
import Paper2.HeightOne.Progress

/-! The fixed-number-field bound applies to every actual finite subgroup of
PGL₂, and thus closes the arithmetic premise of source Lemma 5.6. -/
namespace Paper2.HeightOne.GroupSplit
open MatrixGroup
noncomputable section
variable {L : Type*} [Field L] [NumberField L]

/-- The cardinality bound is uniform over all finite subgroups of the genuine
quotient PGL₂ of one fixed number field. No finite-subgroup classification is
needed for this slightly coarser bound. -/
theorem card_finite_pglSubgroup_le_uniformBound (H : Subgroup (PGL2 L)) [Finite H] :
    Nat.card H ≤ uniformProjectiveBound (Module.finrank ℚ L) := by
  let U := H.comap (pglMk L)
  let G : Set (Binary (K := L)) := (fun A : Matrix.GeneralLinearGroup Bool L =>
    (A : Binary (K := L))) '' (U : Set (Matrix.GeneralLinearGroup Bool L))
  have hdet : ∀ T ∈ G, Matrix.det T ≠ 0 := by
    rintro T ⟨A, hA, rfl⟩
    exact Matrix.GeneralLinearGroup.det_ne_zero A
  have hmul : ∀ T ∈ G, ∀ V ∈ G, T * V ∈ G := by
    rintro T ⟨A, hA, rfl⟩ V ⟨B, hB, rfl⟩
    exact ⟨A * B, U.mul_mem hA hB, rfl⟩
  have htorsion : ∀ T ∈ G, ProjectivelyFinite T := by
    rintro T ⟨A, hA, rfl⟩
    apply (isOfFinOrder_pglMk_iff A).mp
    obtain ⟨n, hn, hp⟩ := (isOfFinOrder_of_finite (⟨pglMk L A, hA⟩ : H)).exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg Subtype.val hp⟩
  have he : projectiveClass '' G = pglToProjectiveClass '' (H : Set (PGL2 L)) := by
    ext q
    constructor
    · rintro ⟨T, ⟨A, hA, rfl⟩, rfl⟩
      exact ⟨pglMk L A, hA, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      obtain ⟨A, rfl⟩ := QuotientGroup.mk'_surjective (scalarSubgroup L) q
      exact ⟨(A : Binary (K := L)), ⟨A, hq, rfl⟩, rfl⟩
  have h := ncard_projective_image_le_uniformBound hdet hmul htorsion
  rw [he, Set.ncard_image_of_injective _ pglToProjectiveClass_injective] at h
  exact h

/-- Source Lemma 5.6 in the original mathematical language: strictly growing
finite subgroups of a fixed PGL₂(number field), paired with nonincreasing
minimal nonbinary arity, cannot make infinitely many strict updates. -/
theorem no_infinite_fixed_field_updates :
    ¬ ∃ (H : ℕ → Subgroup (PGL2 L)) (ν : ℕ → ℕ),
      (∀ i, Finite (H i)) ∧ (∀ i, 3 ≤ ν i) ∧
      (∀ i, H i ≤ H (i + 1)) ∧ (∀ i, ν (i + 1) ≤ ν i) ∧
      (∀ i, H i ≠ H (i + 1) ∨ ν (i + 1) < ν i) := by
  rintro ⟨H, ν, hfin, hν, hincl, hmono, hstrict⟩
  letI (i : ℕ) : Finite (H i) := hfin i
  let S (i : ℕ) : Finset (PGL2 L) := (Set.toFinite (H i : Set (PGL2 L))).toFinset
  have hmem (i : ℕ) (q : PGL2 L) : q ∈ S i ↔ q ∈ H i := Set.Finite.mem_toFinset _
  have hcard (i : ℕ) : (S i).card = Nat.card (H i) := by
    change (Set.toFinite (H i : Set (PGL2 L))).toFinset.card = _
    rw [← Set.ncard_eq_toFinset_card (H i : Set (PGL2 L)) (Set.toFinite _)]
    rfl
  apply no_infinite_strict_updates (uniformProjectiveBound (Module.finrank ℚ L))
  refine ⟨fun i => ⟨(S i).card, ν i, hν i⟩, ?_⟩
  intro i
  apply strictUpdate_of_nested (hν i) (hν (i + 1))
  · intro q hq
    exact (hmem (i + 1) q).mpr (hincl i ((hmem i q).mp hq))
  · rw [hcard]
    exact card_finite_pglSubgroup_le_uniformBound (H (i + 1))
  · exact hmono i
  · rcases hstrict i with hne | hlt
    · left
      intro he
      apply hne
      ext q
      rw [← hmem i q, he, hmem (i + 1) q]
    · exact Or.inr hlt

end
end Paper2.HeightOne.GroupSplit
