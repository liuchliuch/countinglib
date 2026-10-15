import Paper2.Paper1ProvedHardness
import Paper2.SourceFaithful.LocalInputs
import Holant.Proofs.Hardness.GeneralEOUniversalSource
import Holant.Proofs.LinearProgramming.Integration.EOOriginalFamilySource

/-! Genuine source Theorem 2.16 on the original literal family. Its positive
branch runs the proved EO linear programme; its negative branch imports the
universal controlled source, including nonclosed ARS and zero/nullary handling.
The canonical answer adapters execute fixed rational matrices. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Paper2.TractableAlgorithms.Paper1Machine
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem eoPreprocessed (L : Language) (hp : Preprocessed L.family) :
    Holant.Tractable.preprocess L.family = L.family :=
  Holant.Tractable.preprocess_eq_self hp

theorem eoCentral (L : Language) (he : ∀ g ∈ L.family, IsEO g) :
    ∀ i,Holant.Signature.CentralSupport (signatures L i) := by
  intro i
  exact (he _ ⟨i,rfl⟩).2

def eoComputes (L : Language) (hp : Preprocessed L.family) (ht : EOTract L.family) :
    Paper2.Complexity.BinaryCompose.Computes (inputEncoding L)
      (FixedFieldOutput.answerEncoding L) (FixedFieldOutput.answer .nativeX L) := by
  let G := signatures L
  have ht' : Holant.Tractable.EOTract
      (Holant.Tractable.preprocess
        (Holant.LocalDrafts.Tractability.EOEvaluation.Source.signatureSet G)) := by
    change Holant.Tractable.EOTract (Holant.Tractable.preprocess L.family)
    rw [eoPreprocessed L hp]
    exact (eoTract_iff _).mp ht
  let F := Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOOriginalFamilySource.presentation G
  let f := Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOOriginalFamilySource.value G
  let m := Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOOriginalFamilySource.computes G ht'
  apply fieldEvaluation L .nativeX (sourceEncoding L) F f
    (Holant.Algebraic.familyField
      (OriginalFamily.coefficient G Holant.LocalDrafts.Hardness.RootPreprocessing.nativeX)).val.toLinearMap m
    (input L) (input_bytes L)
  intro r
  change (Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOOriginalFamilySource.value
    G (input L r) : AlgebraicComplex) = _
  rw [Holant.LocalDrafts.RemoteWork.RationalLP.Integration.EOOriginalFamilySource.answer_ambient]
  have h := network_value .nativeX L r
  rw [show Paper2.Paper1Proved.kernels .nativeX =
    Holant.LocalDrafts.Hardness.RootPreprocessing.nativeX from rfl] at h
  exact h

theorem eoHard (L : Language) (hp : Preprocessed L.family)
    (he : ∀ g ∈ L.family,IsEO g) (hn : ¬EOTract L.family) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  let G := signatures L
  let F := GeneralOriginalTarget.originalPresentation G
  let f := GeneralOriginalTarget.originalValue G
  let embed : GeneralOriginalTarget.originalField G →ₗ[ℚ] AlgebraicComplex :=
    (GeneralOriginalTarget.originalField G).val.toLinearMap
  have negative : ¬Holant.Tractable.EOTract
      (Holant.Tractable.preprocess (GeneralEOUniversalSource.R.family G)) := by
    change ¬Holant.Tractable.EOTract (Holant.Tractable.preprocess L.family)
    rw [eoPreprocessed L hp]
    exact fun h => hn ((eoTract_iff _).mpr h)
  apply canonicalFieldHard .nativeX L F embed Subtype.val_injective f
  · intro r
    change (GeneralOriginalTarget.originalValue G r : AlgebraicComplex) = _
    rw [GeneralOriginalTarget.target_exact]
    have h := network_value .nativeX L ((inputIso L).symm r)
    change (((inputIso L) ((inputIso L).symm r)).val.realize
      (((inputIso L) ((inputIso L).symm r)).property) G (kernels .nativeX)).denote Fin.elim0 = _ at h
    rw [Equiv.apply_symm_apply] at h
    rw [show Paper2.Paper1Proved.kernels .nativeX =
      (fun _ : Fin 1 => Holant.Signature.disequality) from rfl] at h
    exact h
  · intro A ea count w
    exact ⟨GeneralEOUniversalSource.source G (eoCentral L he) negative w⟩

/-- An inhabitant proved from the actual EO implementation and source. -/
def eoProvider : SourceFaithful.Paper1EOAccepted where
  eo_2_16 L hp he :=
    ⟨fun ht => ⟨eoComputes L hp ht⟩,fun hn => eoHard L hp he hn⟩

end
end Paper2.Paper1Proved
