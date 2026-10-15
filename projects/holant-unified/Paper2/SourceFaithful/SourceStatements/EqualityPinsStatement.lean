import Paper2.SourceFaithful.SourceStatements.EqualityPins
import Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityPins
import Paper2.SourceFaithful.SourceStatements.PublicReduction

/-! Source Corollary 3.5 in both original graph models and in the strict
public root format. The enlargement convention is expressed by executed
reductions in both directions; literal pin realizability is not asserted.
The target oracle may choose any correct polynomial-length minimal root
descriptors, because the closed reverse codec is executed at every query.
-/
namespace Paper2.SourceFaithful.SourceStatements.EqualityPins
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
noncomputable section

/-- Both unit pins may be retained in a finite Turing-equivalent language
when the original language contains a literal equality of arity at least four.
All unrelated original signatures, including zero and nullary rows, survive.
-/
theorem corollary_3_5 (w : Wiring) (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language,
      M.family = L.family ∪ Set.range (fun b : Bool =>
        (⟨1,TensorDecomposition.literalPin b⟩ : AnySignature AlgebraicComplex)) ∧
      Problem.Reduces w M L ∧ Problem.Reduces w L M := by
  have h : ∃ M : Language,
      M.family = L.family ∪ Set.range (fun b : Bool =>
        (⟨1,TensorDecomposition.literalPin b⟩ : AnySignature AlgebraicComplex)) ∧
      FixedFieldOutput.Reduces w M L ∧ FixedFieldOutput.Reduces w L M := by
    cases w with
    | ordinary => exact OrdinaryEqualityPins.corollary_3_5_ordinary L hd heq
    | nativeX => exact corollary_3_5_native L hd heq
  obtain ⟨M,hM,hML,hLM⟩ := h
  exact ⟨M,hM,PublicReduction.of_fixed_field w M L hML,
    PublicReduction.of_fixed_field w L M hLM⟩

end
end Paper2.SourceFaithful.SourceStatements.EqualityPins

