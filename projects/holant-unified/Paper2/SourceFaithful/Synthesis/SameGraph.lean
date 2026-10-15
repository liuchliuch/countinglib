import Paper2.FixedFieldOutput.Holography
import Paper2.Synthesis.OrdinaryTransport

/-! Source-faithful fixed-field adapters on byte-identical graph instances.
The rational-coordinate conversion is an actual proved machine; the older
strict-root same-machine claim is neither used nor inferred. -/
namespace Paper2.FixedFieldOutput
open Paper2.Problem Paper2.ExactInput

theorem SharpPHard.sameGraph {ws wt : Wiring} {A B : Language}
    (h : SharpPHard ws A) (e : Instance A ≃ Instance B)
    (hb : ∀ G, (inputEncoding B).encode (e G) = (inputEncoding A).encode G)
    (hv : ∀ G, value wt B (e G) = value ws A G) : SharpPHard wt B :=
  hard_of_sameValue ws wt A B e (sameBytesComputes A B e hb) (fun G => (hv G).symm) h

end Paper2.FixedFieldOutput

namespace Paper2.SourceFaithful.Synthesis
open Paper2.Problem Paper2.ExactInput Paper2.Synthesis

theorem ordinary_hard_iff_inverseK_native (L : Language) :
    FixedFieldOutput.SharpPHard .ordinary L ↔
      FixedFieldOutput.SharpPHard .nativeX (inverseKLanguage L) := by
  constructor
  · intro h
    exact h.sameGraph (inverseKInstanceEquiv L)
      (inverseKInstance_bytes L) (inverseKInstance_value L)
  · intro h
    apply h.sameGraph (inverseKInstanceEquiv L).symm
    · intro G
      exact (inverseKInstance_bytes L ((inverseKInstanceEquiv L).symm G)).symm.trans
        (congrArg _ ((inverseKInstanceEquiv L).apply_symm_apply G))
    · intro G
      exact (inverseKInstance_value L ((inverseKInstanceEquiv L).symm G)).symm.trans
        (congrArg _ ((inverseKInstanceEquiv L).apply_symm_apply G))

end Paper2.SourceFaithful.Synthesis
