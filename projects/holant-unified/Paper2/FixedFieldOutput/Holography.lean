import Paper2.FixedFieldOutput.Reductions
import Paper2.ExactInput.Computation.NativeHolography

/-! Ordinary/native-X fixed-family equivalence on the exact same serialized
 graph records. Only the answer's finite rational coordinates are converted by
 the explicit fixed-matrix program. No uniform varying-table K-converter is used. -/
namespace Paper2.FixedFieldOutput
open Paper2.ExactInput Paper2.ExactInput.Computation Paper2.Problem
noncomputable section

 theorem native_booleanFP_iff (L : Language) :
    BooleanFP .nativeX L ↔ BooleanFP .ordinary (kLanguage L) := by
  constructor
  · intro h
    apply booleanFP_of_sameValue .ordinary .nativeX (kLanguage L) L (kInstanceEquiv L).symm
      (sameBytesComputes _ _ _ (fun _ => rfl)) _ h
    intro G
    simpa using kInstance_value L ((kInstanceEquiv L).symm G)
  · intro h
    exact booleanFP_of_sameValue .nativeX .ordinary L (kLanguage L) (kInstanceEquiv L)
      (sameBytesComputes _ _ _ (fun _ => rfl)) (fun G => (kInstance_value L G).symm) h

 theorem native_hard_iff (L : Language) :
    SharpPHard .nativeX L ↔ SharpPHard .ordinary (kLanguage L) := by
  constructor
  · intro h
    exact hard_of_sameValue .nativeX .ordinary L (kLanguage L) (kInstanceEquiv L)
      (sameBytesComputes _ _ _ (fun _ => rfl)) (fun G => (kInstance_value L G).symm) h
  · intro h
    apply hard_of_sameValue .ordinary .nativeX (kLanguage L) L (kInstanceEquiv L).symm
      (sameBytesComputes _ _ _ (fun _ => rfl)) _ h
    intro G
    simpa using kInstance_value L ((kInstanceEquiv L).symm G)

end
end Paper2.FixedFieldOutput
