import Paper2.HeightOne.GroupSplit.Accepted
import Paper2.HeightOne.PhaseCards.FieldSaturation
import Holant.Proofs.FiniteGroups.Classification
import Holant.Projective.BoundedTorsion.Source

/-! The two finite-group inputs are obtained from the proved Paper 1
classification and number-field torsion theorem. For torsion, the actual
transfer set is pulled back to matrices over the original coefficient field;
the scalar used to normalize a gadget is retained explicitly. -/
namespace Paper2.HeightOne.GroupSplit
open MatrixGroup Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem provedFinitePGLTypes (H : Subgroup (PGL2 ℂ)) (hH : Finite H) :
    FinitePGLTypes H := by
  let H₁ : Subgroup (Holant.Projective.BoundedTorsion.PGL2 ℂ) := H
  let : Finite H₁ := hH
  rcases Holant.LocalDrafts.FinitePGL2.finite_subgroup_classification H₁ with h | h
  · rcases h with ⟨g,ω,m,_,hω,he⟩ | ⟨g,ω,m,hm,hω,he⟩ | ⟨g,he⟩ | ⟨g,he⟩
    · let e := Holant.LocalDrafts.FinitePGL2.conjugacyEquiv H₁ _ g he
      apply FinitePGLTypes.of_equiv e
      left
      change IsCyclic (Subgroup.zpowers _)
      infer_instance
    · let e := Holant.LocalDrafts.FinitePGL2.conjugacyEquiv H₁ _ g he
      obtain ⟨d⟩ := Holant.Projective.FiniteSubgroupClassification.dihedralModel_isomorphism hω
      exact Or.inr (Or.inl ⟨m,hm,⟨e.trans d.symm⟩⟩)
    · let e := Holant.LocalDrafts.FinitePGL2.conjugacyEquiv H₁ _ g he
      exact Or.inr (Or.inr (Or.inl ⟨e.trans
        Holant.Projective.FiniteGroupFacts.tetrahedral_iso_A4⟩))
    · let e := Holant.LocalDrafts.FinitePGL2.conjugacyEquiv H₁ _ g he
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans
        Holant.Projective.FiniteGroupFacts.octahedral_iso_S4⟩)))
  · obtain ⟨e⟩ := h.nonempty_mulEquiv
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans
      Holant.Projective.FiniteGroupFacts.icosahedral_iso_A5⟩)))

theorem projectivelyFinite_of_map {K E : Type*} [Field K] [Field E]
    (f : K →+* E) (T : Binary (K := K))
    (h : ProjectivelyFinite (T.map f)) : ProjectivelyFinite T := by
  obtain ⟨r,hr,c,hc,he⟩ := h
  have hm : (T ^ r).map f = c • ((1 : Binary (K := K)).map f) := by
    simpa only [Matrix.map_pow,Matrix.map_one _ f.map_zero f.map_one] using he
  obtain ⟨d,hd,hTd⟩ := scalar_descends f (by exact one_ne_zero) hc hm
  exact ⟨r,hr,d,hd,hTd⟩

theorem provedBoundedTorsion
    (L : IntermediateField ℚ AlgebraicComplex) (hL : FiniteDimensional ℚ L)
    (F : SignatureFamily AlgebraicComplex) (hF : ∀ f ∈ F, ∀ x, f.2 x ∈ L)
    (hne : (actualTransfers F).Nonempty)
    (ht : ∀ B, ActualNonsingular F B → ProjectivelyFinite (transfer B)) :
    (projectiveClass '' actualTransfers F).Finite := by
  let : FiniteDimensional ℚ L := hL
  let : NumberField L := { to_charZero := inferInstance, to_finiteDimensional := hL }
  let E : Subfield AlgebraicComplex := L.toSubfield
  let : NumberField E := inferInstanceAs (NumberField L)
  let S : Set (Binary (K := E)) := {T | T.map E.subtype ∈ actualTransfers F}
  let hG := actualTransfers_projectiveMatrixGroup F hne ht
  have hdet : ∀ T ∈ S, Matrix.det T ≠ 0 := by
    intro T hT hz
    have h := hG.det_ne_zero hT
    apply h
    change Matrix.det (E.subtype.mapMatrix T) = 0
    rw [← E.subtype.map_det,hz,map_zero]
  have hmul : ∀ T ∈ S, ∀ U ∈ S, T * U ∈ S := by
    intro T hT U hU
    change (T * U).map E.subtype ∈ actualTransfers F
    rw [Matrix.map_mul]
    exact hG.mul_mem _ hT _ hU
  have htor : ∀ T ∈ S, ProjectivelyFinite T := by
    intro T hT
    apply projectivelyFinite_of_map E.subtype
    obtain ⟨B,hB,c,hc,he⟩ := hT
    rw [he]
    exact (ht B hB).smul hc
  have hs : (projectiveClass '' S).Finite := by
    change (Holant.Projective.BoundedTorsion.projectiveClass '' S).Finite
    exact Holant.Projective.BoundedTorsion.finite_projective_image_of_torsion
      hdet hmul htor
  apply (hs.image (extendProjectiveClass E.subtype)).subset
  rintro _ ⟨T,⟨B,hB,c,hc,rfl⟩,rfl⟩
  have hfield : ∀ f ∈ F, PhaseCards.ProjectivelyOver E f.2 := by
    intro f hf
    exact ⟨1,one_ne_zero,fun x => by simpa only [one_mul,E,
      IntermediateField.mem_toSubfield] using hF f hf x⟩
  obtain ⟨d,hd,hcoeff⟩ := PhaseCards.network_projectivelyOver E hfield hB.1
  let V : Binary (K := E) := fun i j => ⟨d * transfer B i j, by
    cases j <;> simpa [transfer,binarySignature,Matrix.mul_apply,X,Signature.disequality,
      Fintype.sum_bool] using hcoeff ![i,_]⟩
  have hV : V.map E.subtype = d • transfer B := rfl
  have hVS : V ∈ S := by
    change V.map E.subtype ∈ actualTransfers F
    rw [hV]
    exact ⟨B,hB,d,hd,rfl⟩
  refine ⟨projectiveClass V,⟨V,hVS,rfl⟩,?_⟩
  rw [extendProjectiveClass_apply,hV,projectiveClass_smul _ hd,
    projectiveClass_smul _ hc]

theorem provedPaper1 : Paper1Accepted where
  finitePGLTypes_2_1 := provedFinitePGLTypes
  boundedTorsion_5_2 := provedBoundedTorsion

end
end Paper2.HeightOne.GroupSplit
