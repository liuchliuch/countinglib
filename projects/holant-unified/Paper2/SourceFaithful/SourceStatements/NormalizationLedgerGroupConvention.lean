import Paper2.SourceFaithful.SourceStatements.NormalizationLedgerGroups
import Paper2.HeightOne.GroupSplit.Source

/-! Honest transfer-group conventions at empty and safe nonempty languages.
The native through-wire contributes the identity; its use does not assert
that the vertex-port model has an arity-two network with no vertices. -/
namespace Paper2.SourceFaithful.SourceStatements.NormalizationLedger
noncomputable section
open Tractable Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

def transferGroup (F : SignatureFamily AlgebraicComplex) : Subgroup (PGL2 AlgebraicComplex) :=
  Subgroup.closure (actualClasses F)

theorem pullbackGroup_eq_conjugate (A : InvertibleKernel)
    (F : SignatureFamily AlgebraicComplex) :
    pullbackGroup A F =
      (transferGroup F).map (MulAut.conj ((basisClass A)⁻¹)).toMonoidHom := by
  rw [transferGroup, MonoidHom.map_closure]
  rfl

lemma transferGroup_safe (F : SignatureFamily AlgebraicComplex)
    (hsafe : AllBinariesSafe F) (hne : (actualTransfers F).Nonempty) :
    ∃ hG : ProjectiveMatrixGroup (actualTransfers F),
      transferGroup F = projectiveSubgroup hG := by
  have htorsion : ∀ B, ActualNonsingular F B → ProjectivelyFinite (transfer B) := by
    intro B hB
    apply (hsafe B hB.1 ?_).2
    intro hz
    apply hB.2
    rw [hz, Matrix.det_zero]
  let hG := actualTransfers_projectiveMatrixGroup F hne htorsion
  exact ⟨hG, closure_actualClasses F hG⟩

lemma transferGroup_no_actual_classes (F : SignatureFamily AlgebraicComplex)
    (hF : actualClasses F = ∅) : transferGroup F = ⊥ := by
  rw [transferGroup, hF, Subgroup.closure_empty]

end
end Paper2.SourceFaithful.SourceStatements.NormalizationLedger

