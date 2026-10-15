import Paper2.Paper1ProvedRecognition.Source
import Paper2.Paper1ProvedHardness
import Paper2.TractableAlgorithms.Paper1Evaluation
import Paper2.SourceFaithful.Paper1Accepted

/-! The actual source input record is inhabited by the independently proved
uniform recognizer, complete seven-clause graph machines and controlled source
hardness. No accepted classification premise is required. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput
noncomputable section

def provider : SourceFaithful.Paper1Accepted where
  recognition_2_22 := ⟨Paper1ProvedRecognition.recognizer⟩
  evaluation_2_22 := TractableAlgorithms.ordinary_booleanFP_of_tract
  literalEquality_1_2 L he :=
    ⟨TractableAlgorithms.native_booleanFP_of_tractX L,
      literalEqualityHard L he⟩
  equalityAnchor_2_13 := equalityAnchor
  primeQuaternary_1_3 L hq :=
    ⟨TractableAlgorithms.native_booleanFP_of_tract L,quaternaryHard L hq⟩

end
end Paper2.Paper1Proved
