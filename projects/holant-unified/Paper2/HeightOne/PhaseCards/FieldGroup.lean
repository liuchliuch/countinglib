import Paper2.HeightOne.PhaseCards.DiagonalFieldSaturation
import Paper2.HeightOne.GroupSplit.FieldMap
import Paper2.HeightOne.UniformBound.Progress

/-! The complete safe group, pulled back through the current diagonal basis,
lives in the image of the one frozen coefficient field inside algebraic
complex PGL₂. No different field is selected after a normalization. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable GroupSplit GroupSplit.MatrixGroup

lemma pglMk_mem_subfield_range (E : Subfield AlgebraicComplex)
    (U : Matrix.GeneralLinearGroup Bool AlgebraicComplex)
    (hfield : ∃ c : AlgebraicComplex, c ≠ 0 ∧ ∀ i j, c * (U : AMat) i j ∈ E) :
    pglMk AlgebraicComplex U ∈ (pglMap E.subtype).range := by
  obtain ⟨c, hc, hcoeff⟩ := hfield
  let V : Matrix Bool Bool E := fun i j => ⟨c * (U : AMat) i j, hcoeff i j⟩
  have hmap : V.map E.subtype = c • (U : AMat) := rfl
  have hdmap : Matrix.det (V.map E.subtype) ≠ 0 := by
    rw [hmap, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ hc) (Matrix.GeneralLinearGroup.det_ne_zero U)
  have hd : Matrix.det V ≠ 0 := by
    intro hz
    apply hdmap
    change Matrix.det (E.subtype.mapMatrix V) = 0
    rw [← E.subtype.map_det, hz, map_zero]
  let W := Matrix.GeneralLinearGroup.mkOfDetNeZero V hd
  refine ⟨pglMk E W, ?_⟩
  rw [pglMap_mk]
  apply pglMk_eq_iff_projectiveClass_eq.mpr
  change projectiveClass (V.map E.subtype) = projectiveClass (U : AMat)
  rw [hmap]
  exact projectiveClass_smul _ hc

/-- Every actual projective transfer over a projectively E-valued family is a
class from the actual quotient PGL₂(E). -/
theorem actualClasses_in_subfield_range (E : Subfield AlgebraicComplex)
    {F : SignatureFamily AlgebraicComplex} (hF : ∀ f ∈ F, ProjectivelyOver E f.2) :
    actualClasses F ⊆ (pglMap E.subtype).range := by
  rintro q ⟨U, ⟨B, ⟨hreal, hdet⟩, d, hd, hU⟩, rfl⟩
  obtain ⟨c, hc, hcoeff⟩ := network_projectivelyOver E hF hreal
  have hbcoeff (i j : Bool) : c * B i j ∈ E := hcoeff ![i, j]
  have htcoeff (i j : Bool) : c * transfer B i j ∈ E := by
    cases j <;> simpa [transfer, Matrix.mul_apply, X, Signature.disequality,
      Fintype.sum_bool] using hbcoeff i _
  apply pglMk_mem_subfield_range E U
  refine ⟨c / d, div_ne_zero hc hd, ?_⟩
  intro i j
  rw [hU]
  change (c / d) * (d * transfer B i j) ∈ E
  rw [← mul_assoc, div_mul_cancel₀ _ hd]
  exact htcoeff i j

/-- A legal diagonal normalization cancels after pullback. The result is a
literal inclusion in the canonical PGL₂(E) image, for all actual binary gadgets. -/
theorem pulledback_actualClasses_in_subfield_range (E : Subfield AlgebraicComplex)
    (A : InvertibleKernel) (a b : AlgebraicComplex)
    (hA : A.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    {F : SignatureFamily AlgebraicComplex} (hF : ∀ f ∈ F, PullbackOver E A f) :
    (fun q => (pglMk _ (basisGL A))⁻¹ * q * pglMk _ (basisGL A)) '' actualClasses F ⊆
      (pglMap E.subtype).range := by
  have hfield : ∀ f ∈ familyAction A.symm F, ProjectivelyOver E f.2 := by
    rintro f ⟨g, hg, rfl⟩
    exact hF g hg
  have h := actualClasses_in_subfield_range E hfield
  have hi : A.symm.matrix = diagonalKernel a⁻¹ b⁻¹ := inverse_diagonal A a b hA ha hb
  rw [completeClasses_diagonal_transport F A.symm a⁻¹ b⁻¹ hi (inv_ne_zero ha) (inv_ne_zero hb)] at h
  simpa only [basisGL_symm, map_inv, inv_inv] using h

/-- Canonical descent of a subgroup contained in the field image. -/
def descendFieldGroup (E : Subfield AlgebraicComplex) (H : Subgroup (PGL2 AlgebraicComplex)) :
    Subgroup (PGL2 E) := H.comap (pglMap E.subtype)

lemma descendFieldGroup_map (E : Subfield AlgebraicComplex) (H : Subgroup (PGL2 AlgebraicComplex))
    (hH : H ≤ (pglMap E.subtype).range) :
    (descendFieldGroup E H).map (pglMap E.subtype) = H := by
  exact Subgroup.map_comap_eq_self hH

/-- The numerical bound for a finite group descended to the same number field.
No finite coefficient extension is chosen in this theorem. -/
theorem card_descendFieldGroup_le (E : Subfield AlgebraicComplex) [NumberField E]
    (H : Subgroup (PGL2 AlgebraicComplex)) [Finite H] :
    Nat.card (descendFieldGroup E H) ≤ uniformProjectiveBound (Module.finrank ℚ E) := by
  haveI : Finite (descendFieldGroup E H) := Finite.of_injective
    (fun q : descendFieldGroup E H => (⟨pglMap E.subtype q, q.property⟩ : H))
    (fun a b h => Subtype.ext (pglMap_injective E.subtype (congrArg Subtype.val h)))
  exact card_finite_pglSubgroup_le_uniformBound _

end
end Paper2.HeightOne.PhaseCards
