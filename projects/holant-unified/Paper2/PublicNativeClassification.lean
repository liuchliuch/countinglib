import Paper2.PublicDichotomyComplete
import Paper2.Paper1ProvedRecognition.NativeSource
import Paper2.ExactInput.Recognition.NativeComplete

/-! Effective public classification in the original native-X coordinates.
Both recognizers are actual fixed finite machines before the varying exact
table input. Evaluation and hardness retain the original literal graph input
and strict minimal-polynomial/isolating-rectangle output convention. -/
namespace Paper2.PublicDichotomy
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
noncomputable section

/-- Source Theorem 9.2, including the effective decision of its applicable side
from every valid exact native table list. -/
theorem theorem_9_2 :
    ∃ r : NativeTractRecognizer,
      (∀ raw : RawLanguage, ∀ hraw : raw.Valid,
        ∃ b : Bool, ∃ steps : ℕ,
          (fun c : Option r.machine.tm.Cfg => c.bind r.machine.tm.step)^[steps]
            (some (r.initial raw)) = some (r.final b) ∧
          r.machine.tm.step (r.final b) = none ∧
          (b = true ↔ Tract (kImage (⟨raw,hraw⟩ : Language)))) ∧
      (∀ L : Language,
        (r.decision L = true ↔ Tract (kImage L)) ∧
        (Tract (kImage L) → Problem.InFP .nativeX L) ∧
        (¬Tract (kImage L) → Problem.SharpPHard .nativeX L)) := by
  refine ⟨Paper1ProvedRecognition.NativeSource.recognizer,
    Paper1ProvedRecognition.NativeSource.recognizer.total_correct,?_⟩
  intro L
  exact ⟨Paper1ProvedRecognition.NativeSource.recognizer.correct L,
    TractableAlgorithms.native_public_inFP_of_tract L,native_hardness L⟩

/-- The full public theorem with ordinary and native effective recognition.
There is no source promise, arity restriction, or accepted classification
argument in either original input domain. -/
theorem main_theorem_with_native_recognition :
    ∃ ordinary : TractRecognizer, ∃ native : NativeTractRecognizer,
      (∀ raw : RawLanguage, ∀ hraw : raw.Valid,
        ∃ b : Bool, ∃ steps : ℕ,
          (fun c : Option ordinary.machine.tm.Cfg => c.bind ordinary.machine.tm.step)^[steps]
            (some (ordinary.initial raw)) = some (ordinary.final b) ∧
          ordinary.machine.tm.step (ordinary.final b) = none ∧
          (b = true ↔ Tract (Language.family ⟨raw,hraw⟩))) ∧
      (∀ raw : RawLanguage, ∀ hraw : raw.Valid,
        ∃ b : Bool, ∃ steps : ℕ,
          (fun c : Option native.machine.tm.Cfg => c.bind native.machine.tm.step)^[steps]
            (some (native.initial raw)) = some (native.final b) ∧
          native.machine.tm.step (native.final b) = none ∧
          (b = true ↔ Tract (kImage (⟨raw,hraw⟩ : Language)))) ∧
      (∀ L : Language,
        (ordinary.decision L = true ↔ Tract L.family) ∧
        (native.decision L = true ↔ Tract (kImage L)) ∧
        (Tract L.family → Problem.InFP .ordinary L) ∧
        (¬Tract L.family → Problem.SharpPHard .ordinary L) ∧
        (Tract (kImage L) → Problem.InFP .nativeX L) ∧
        (¬Tract (kImage L) → Problem.SharpPHard .nativeX L)) := by
  obtain ⟨ordinary,hrun,hordinary,_⟩ := main_theorem
  refine ⟨ordinary,Paper1ProvedRecognition.NativeSource.recognizer,hrun,
    Paper1ProvedRecognition.NativeSource.recognizer.total_correct,?_⟩
  intro L
  exact ⟨(hordinary L).1,Paper1ProvedRecognition.NativeSource.recognizer.correct L,
    (hordinary L).2.1,(hordinary L).2.2,
    TractableAlgorithms.native_public_inFP_of_tract L,native_hardness L⟩

end
end Paper2.PublicDichotomy

