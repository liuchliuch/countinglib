import Paper2.SourceFaithful.Synthesis.InitialBranches

/-! The unary input used by the local Paper 2 routes follows from the exact
ordinary odd theorem already used in the main preparation.  The proved
same-graph K transport, preprocessing equivalence and literal restriction
return its conclusion to the original native-X language. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput Paper2.SourceFaithful

/-- A nonzero literal unary gives the odd branch in the original language,
including arbitrary zero and nullary labels elsewhere in that language. -/
theorem unaryFromOdd (PO : SourceFaithful.Paper1OddAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted)
    (L : Language) (u : Signature AlgebraicComplex 1) (hu : u ≠ 0)
    (hmem : (⟨1,u⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  apply SourceFaithful.Synthesis.odd_classification PO PR L
  exact ⟨⟨1,u⟩,hmem,by exact ⟨0,rfl⟩,hu⟩

/-- No separate unary classification input is required when the ordinary odd
theorem and literal restriction are available.  The odd theorem remains an
explicit upstream theorem input to this derived provider. -/
def unaryProviderOfOdd (PO : SourceFaithful.Paper1OddAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) :
    SourceFaithful.Paper1UnaryAccepted where
  unary_3_4 := unaryFromOdd PO PR

end Paper2.Paper1Proved
