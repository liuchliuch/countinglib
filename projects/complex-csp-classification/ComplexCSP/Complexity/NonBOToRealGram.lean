import ComplexCSP.Complexity.NonBOToGram
import ComplexCSP.Algebra.RealGramReduction

/-! # The ordered-real obstruction endpoint for the remaining hardness theorem -/
namespace ComplexCSP.ComplexityNonBOToRealGram
open PlanarHom.Complexity ComplexityReducedGram
variable {D : Type} [Fintype D] {s : ℕ}

/-- Literal non-BO supplies a finite nonnegative Gram problem over an actual
ordered algebraic real field and a charged reduction to the original input
language. Every field, basis and intermediate presentation is constructed by
the preceding theorems; no hardness assumption is made. -/
theorem exists_real_gram (L : Language D ℂ (Fin s))
    (hL : ∀ i a,IsAlgebraic ℚ (L.value i a)) (hnot : ¬JointBO L) :
    ∃ W : Witness L, Nonempty (PromisePolyTimeTuringReduction (RealGramReduction.problem W)
      (ComplexityCSPCountReduction.partitionProblem W.input W.basis)) := by
  obtain ⟨W⟩ := ComplexityNonBOToGram.exists_reduced_gram L hL hnot
  exact ⟨W,⟨RealGramReduction.reduction W⟩⟩

end ComplexCSP.ComplexityNonBOToRealGram
