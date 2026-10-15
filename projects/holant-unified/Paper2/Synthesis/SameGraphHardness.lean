import Paper2.Complexity.OracleSameEncoding
import Paper2.Problem
import Paper2.ExactInput.Computation.NativeHolography

/-! Exact hardness transfer on the original graph bytes, including arbitrary
zero and nullary labels.  There is no preprocessing cost, root conversion, or
extra accepted Paper 1 theorem: the original oracle program is used unchanged. -/
namespace Paper2.Problem
open Paper2.ExactInput Paper2.Complexity

/-- A semantic graph equivalence preserves bounded public-root conventions when
its two graph encodings are literally identical. -/
noncomputable def BoundedAnswers.sameGraph {w v : Wiring} {L M : Language}
    (a : BoundedAnswers v M) (e : Instance L ≃ Instance M)
    (bytes : ∀ G, (inputEncoding M).encode (e G) = (inputEncoding L).encode G)
    (values : ∀ G, value v M (e G) = value w L G) : BoundedAnswers w L where
  answer G := a.answer (e G)
  correct G := by simpa only [values] using a.correct (e G)
  outputBound := {
    bound := a.outputBound.bound
    length_le := fun G => by simpa only [bytes] using a.outputBound.length_le (e G) }

/-- Hardness transfers without compiling any new instructions, because the
source and target oracle receive identical valid strings and return the same
strict minimal-root descriptors under the transported answer convention. -/
theorem SharpPHard.sameGraph {w v : Wiring} {L M : Language}
    (hard : SharpPHard w L) (e : Instance L ≃ Instance M)
    (bytes : ∀ G, (inputEncoding M).encode (e G) = (inputEncoding L).encode G)
    (values : ∀ G, value v M (e G) = value w L G) : SharpPHard v M := by
  have invBytes : ∀ G, (inputEncoding L).encode (e.symm G) =
      (inputEncoding M).encode G := by
    intro G
    exact (bytes (e.symm G)).symm.trans (congrArg _ (e.apply_symm_apply G))
  have invValues : ∀ G, value w L (e.symm G) = value v M G := by
    intro G
    exact (values (e.symm G)).symm.trans (congrArg _ (e.apply_symm_apply G))
  refine ⟨?_, ?_⟩
  · obtain ⟨a⟩ := hard.1
    exact ⟨a.sameGraph e.symm invBytes invValues⟩
  · intro answers f hf
    obtain ⟨r⟩ := hard.2 (answers.sameGraph e bytes values) f hf
    exact ⟨r.sameTarget e bytes (fun _ => rfl)⟩

/-- Fixed-language native-to-ordinary hardness, with the exact normalized K. -/
theorem native_hard_iff_k_ordinary (L : Language) :
    SharpPHard .nativeX L ↔ SharpPHard .ordinary (Computation.kLanguage L) := by
  constructor
  · intro h
    exact h.sameGraph (Computation.kInstanceEquiv L)
      (Computation.kInstance_bytes L) (Computation.kInstance_value L)
  · intro h
    apply h.sameGraph (Computation.kInstanceEquiv L).symm
    · intro G
      exact (Computation.kInstance_bytes L ((Computation.kInstanceEquiv L).symm G)).symm.trans
        (congrArg _ ((Computation.kInstanceEquiv L).apply_symm_apply G))
    · intro G
      exact (Computation.kInstance_value L ((Computation.kInstanceEquiv L).symm G)).symm.trans
        (congrArg _ ((Computation.kInstanceEquiv L).apply_symm_apply G))

end Paper2.Problem
