import Paper2.SourceFaithful.SourceStatements.NormalizationLedgerSteps
import Paper2.HeightOne.PhaseCards.ConformalTransport

/-! The actual transfer subgroup in the one original field. The subgroup
closure supplies the neutral wire also for an empty language; in the safe
nonempty cases it is exactly the previously proved all-realizable subgroup.
No binary-existence or diagonal-coordinate premise is added to the ledger. -/
namespace Paper2.SourceFaithful.SourceStatements.NormalizationLedger
noncomputable section
open Tractable ExactInput Paper2.HeightOne.PhaseCards
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

def basisClass (A : InvertibleKernel) : PGL2 AlgebraicComplex :=
  pglMk AlgebraicComplex (basisGL A)

lemma basisGL_comp (D A : InvertibleKernel) : basisGL (D.comp A) = basisGL D * basisGL A := by
  apply Units.ext
  change Matrix.of (Kernel.mul D.matrix A.matrix) =
    (Matrix.of D.matrix) * (Matrix.of A.matrix)
  ext x y
  simp [Kernel.mul_apply, Matrix.mul_apply, add_comm]

@[simp] lemma basisClass_comp (D A : InvertibleKernel) :
    basisClass (D.comp A) = basisClass D * basisClass A := by
  simp [basisClass, basisGL_comp]

/-- Literal `[A]⁻¹ G [A]` on the complete set of actual binary classes. -/
def pulledbackClasses (A : InvertibleKernel) (F : SignatureFamily AlgebraicComplex) :
    Set (PGL2 AlgebraicComplex) :=
  (fun q => (basisClass A)⁻¹ * q * basisClass A) '' actualClasses F

/-- Include the neutral through-wire and group operations. In every safe
nonempty case this closure adds no nonidentity graph transfer classes. -/
def pullbackGroup (A : InvertibleKernel) (F : SignatureFamily AlgebraicComplex) :
    Subgroup (PGL2 AlgebraicComplex) := Subgroup.closure (pulledbackClasses A F)

lemma closure_actualClasses (F : SignatureFamily AlgebraicComplex)
    (hG : ProjectiveMatrixGroup (actualTransfers F)) :
    Subgroup.closure (actualClasses F) = projectiveSubgroup hG := by
  rw [actualClasses_subgroup hG, Subgroup.closure_eq]

/-- Exact cancellation of the newly applied arbitrary GO(X) matrix. -/
theorem pulledbackClasses_normalize (A D : InvertibleKernel) (hD : XConformal D)
    (F : SignatureFamily AlgebraicComplex) :
    pulledbackClasses (D.comp A) (familyAction D F) = pulledbackClasses A F := by
  unfold pulledbackClasses
  rw [completeClasses_conformal_transport F D hD, Set.image_image, basisClass_comp]
  congr 1
  funext q
  change (basisClass D * basisClass A)⁻¹ *
    (basisClass D * q * (basisClass D)⁻¹) * (basisClass D * basisClass A) = _
  group

theorem pullbackGroup_normalize (A D : InvertibleKernel) (hD : XConformal D)
    (F : SignatureFamily AlgebraicComplex) :
    pullbackGroup (D.comp A) (familyAction D F) = pullbackGroup A F := by
  unfold pullbackGroup
  rw [pulledbackClasses_normalize A D hD F]

theorem pullbackGroup_augment (A : InvertibleKernel)
    {F H : SignatureFamily AlgebraicComplex} (hFH : F ⊆ H) :
    pullbackGroup A F ≤ pullbackGroup A H :=
  Subgroup.closure_mono (Set.image_mono (actualClasses_mono hFH))

/-- The complete actual group descends through the canonical injective
PGL₂(E) homomorphism, with the same fixed field at every index. -/
theorem pullbackGroup_in_original_field (E : Subfield AlgebraicComplex)
    (A : InvertibleKernel) (hA : XConformal A)
    (F : SignatureFamily AlgebraicComplex) (hfield : ∀ f ∈ F, PullbackOver E A f) :
    pullbackGroup A F ≤ (pglMap E.subtype).range := by
  apply (Subgroup.closure_le _).mpr
  exact pulledback_actualClasses_conformal_in_subfield_range E A hA hfield

lemma Ledger.group_in_original_field {E : Subfield AlgebraicComplex}
    {G : Language} {S : State} (h : Ledger E G S) :
    pullbackGroup S.coordinates S.language.family ≤ (pglMap E.subtype).range :=
  pullbackGroup_in_original_field E S.coordinates h.conformal S.language.family h.field

/-- Every allowed step preserves or enlarges the pulled-back group. For
normalization the stronger literal equality is given separately below. -/
lemma LegalStep.group_mono {E : Subfield AlgebraicComplex} {S T : State}
    (step : LegalStep E S T) :
    pullbackGroup S.coordinates S.language.family ≤
      pullbackGroup T.coordinates T.language.family := by
  cases step with
  | augment hA hsub _ _ =>
    rw [hA]
    exact pullbackGroup_augment S.coordinates hsub
  | normalize D hD hA hfamily =>
    rw [hA, hfamily, pullbackGroup_normalize S.coordinates D hD S.language.family]

end
end Paper2.SourceFaithful.SourceStatements.NormalizationLedger

