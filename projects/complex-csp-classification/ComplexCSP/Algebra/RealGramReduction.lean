import ComplexCSP.Algebra.RealGramField
import ComplexCSP.Complexity.CSPFieldTransport
import Mathlib.Algebra.Algebra.Hom.Rat

/-! # The actual ordered-real Gram problem reduces to the original CSP -/
noncomputable section
open Classical
namespace ComplexCSP.RealGramReduction
open ComplexityReducedGram PlanarHom PlanarHom.Complexity
variable {D : Type} [Fintype D] {s : ℕ} {L : Language D ℂ (Fin s)} (W : Witness L)

def problem : PromiseProblem :=
  ComplexityCSPCountReduction.partitionProblem
    (binaryLanguage (RealGramField.matrix W)) (RealGramField.basis W)

theorem mapped_language : (binaryLanguage (RealGramField.matrix W)).mapValues
    (RealGramField.embedding W) = binaryLanguage W.matrix := by
  unfold binaryLanguage Language.mapValues
  congr 1
  funext i a
  exact RealGramField.embedding_matrix W (a 0) (a 1)

/-- The constructed real-field encoding is descended from the actual common
complex-field oracle by a compiled rational-linear left inverse. -/
def toCommon : PromisePolyTimeTuringReduction (problem W)
    (ComplexityCSPCountReduction.partitionProblem (binaryLanguage W.matrix) W.basis) := by
  have h := ComplexityCSPFieldTransport.descentReduction
    (binaryLanguage (RealGramField.matrix W)) (RealGramField.basis W) W.basis
    (RealGramField.embedding W).toRatAlgHom
  change PromisePolyTimeTuringReduction (problem W)
    (ComplexityCSPCountReduction.partitionProblem
      ((binaryLanguage (RealGramField.matrix W)).mapValues (RealGramField.embedding W)) W.basis) at h
  rw [mapped_language] at h
  exact h

/-- Full graph/matrix oracle reduction from the actual ordered algebraic real
field to the original fixed complex input language's exact representation. -/
def reduction : PromisePolyTimeTuringReduction (problem W)
    (ComplexityCSPCountReduction.partitionProblem W.input W.basis) :=
  (toCommon W).trans W.reduction

end ComplexCSP.RealGramReduction
