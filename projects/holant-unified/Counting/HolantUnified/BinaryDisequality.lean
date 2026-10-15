import Holant.Proofs
import Holant.Decidability

/-!
# Binary-disequality Holant: preserved public contracts

Thin wrappers of the closed public results in the fixed B release
`ec3e598e380c57e1c4d1a3c73a4ad1b4f7eed711`.

Evaluation keeps the original family-field output encoding. Recognition consumes
represented algebraic RootCode inputs and has one machine before every family
layout; its execution clock is not asserted to be polynomial. Ordinary Holant
with an added X vertex label, native X edges with a literal I member, and the
native quaternary hypothesis remain different public statements.
-/

noncomputable section
namespace Counting.HolantUnified.BinaryDisequality

open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems (quaternaryData)

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

/-- Manuscript Theorem 1.1: equality edges and one added X vertex label. -/
theorem binaryDisequality : Holant.Statements.BinaryDisequality G :=
  Holant.Theorems.binaryDisequality G

/-- Manuscript Theorem 1.2: native X edges and literal I membership. -/
theorem literalEquality : Holant.Statements.LiteralEquality G :=
  Holant.Theorems.literalEquality G

/-- Manuscript Theorem 1.3: the original native-X family with its quaternary member. -/
theorem quaternary : Holant.Statements.Quaternary G :=
  Holant.Theorems.quaternary G

/-- Manuscript Theorem 2.19: fixed-family evaluation for all seven Tract clauses. -/
theorem tractableEvaluation : Holant.Statements.TractableEvaluation G :=
  Holant.Theorems.tractableEvaluation G

/-- One terminating recognizer for TractX(K(F ∪ {I})) over every exact input layout. -/
theorem binaryDisequality_uniform : ∃ M : BinaryCompose.Machine,
    ∀ (s : ℕ) (a : ℕ → ℕ)
      (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
      (input : OriginalFamilyInput.Input (fun i : Fin s => a i.val))
      (represented : ∀ i x, (input i x).Represents (G i x : ℂ)),
      Nonempty (TM2OutputsInTime M.computer
        (OriginalFamilyPackingMachine.encoding.encode
          (OriginalFamilyPackingSource.fromSource (fun i : Fin s => a i.val) input false))
        (some (RuntimeAugmentedNativeDecision.outputEncoding.encode
          (RuntimeAugmentedNativeDecision.output (PaperBinaryDisequalityDecision.data G input represented))))
        (RuntimeAugmentedNativeDecision.executes.cost
          (PaperBinaryDisequalityDecision.data G input represented))) ∧
      (RuntimeAugmentedNativeDecision.answer (PaperBinaryDisequalityDecision.data G input represented) = true ↔
        TractX (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G ∪
          {(⟨2, kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)}))) :=
  Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems.binaryDisequality_uniform

/-- One terminating recognizer for TractX(K(F)) over every exact input layout. -/
theorem literalEquality_uniform : ∃ M : BinaryCompose.Machine,
    ∀ (s : ℕ) (a : ℕ → ℕ)
      (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
      (input : OriginalFamilyInput.Input (fun i : Fin s => a i.val))
      (represented : ∀ i x, (input i x).Represents (G i x : ℂ)),
      Nonempty (TM2OutputsInTime M.computer
        (OriginalFamilyPackingMachine.encoding.encode
          (OriginalFamilyPackingSource.fromSource (fun i : Fin s => a i.val) input false))
        (some (RuntimeFourDecision.outputEncoding.encode
          (RuntimeFourDecision.output (PaperLiteralEqualityDecision.data G input represented))))
        (RuntimeFourDecision.executes.cost (PaperLiteralEqualityDecision.data G input represented))) ∧
      (PaperLiteralEqualityDecision.answer G input represented = true ↔
        TractX (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G))) :=
  Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems.literalEquality_uniform

/-- One terminating recognizer for Tract(K(F)) over every exact input layout. -/
theorem quaternary_uniform : ∃ M : BinaryCompose.Machine,
    ∀ (s : ℕ) (a : ℕ → ℕ)
      (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
      (input : OriginalFamilyInput.Input (fun i : Fin s => a i.val))
      (represented : ∀ i x, (input i x).Represents (G i x : ℂ)),
      Nonempty (TM2OutputsInTime M.computer
        (OriginalFamilyPackingMachine.encoding.encode
          (OriginalFamilyPackingSource.fromSource (fun i : Fin s => a i.val) input false))
        (some (PaperQuaternaryDecision.RuntimeSevenPrograms.outputEncoding.encode
          (PaperQuaternaryDecision.RuntimeSevenPrograms.output (quaternaryData G input represented))))
        (PaperQuaternaryDecision.RuntimeSevenPrograms.executes.cost
          (quaternaryData G input represented))) ∧
      (PaperQuaternaryDecisionSource.answer (quaternaryData G input represented) = true ↔
        Tract (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G))) ∧
      (PaperQuaternaryDecisionSource.answer (quaternaryData G input represented) = false ↔
        ¬Tract (familyAction sourceKBasis (PaperLiteralEqualityCriterion.family G))) :=
  Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperMainTheorems.quaternary_uniform

/-- One terminating recognizer for all seven clauses on the original family.
The retained output packet and actual execution clock are part of the contract. -/
theorem tractableEvaluation_uniform : ∃ M : BinaryCompose.Machine,
    ∀ d : RuntimeSupportTable.Data,
      Nonempty (TM2OutputsInTime M.computer
        (OriginalFamilyPackingMachine.encoding.encode (RuntimeSupportTable.original d))
        (some (RuntimeSevenPrograms.outputEncoding.encode (RuntimeSevenPrograms.output d)))
        (RuntimeSevenPrograms.executes.cost d)) ∧
      ((RuntimeSevenPrograms.output d).1 = true ↔ Tract (RuntimeSevenDecision.family d)) ∧
      ((RuntimeSevenPrograms.output d).1 = false ↔ ¬Tract (RuntimeSevenDecision.family d)) :=
  Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSevenDecision.uniform_source

end Counting.HolantUnified.BinaryDisequality
end
