import Paper2.SourceFaithful.PublicHardness
import Paper2.SourceFaithful.Synthesis.Complete
import Paper2.Paper1ProvedOddResidueUnaryReduction
import Paper2.Paper1ProvedRecognition.Source

/-! The complete original-language public-output assembly. Every local Paper 2
branch, recognition programme, graph evaluator and strict-root output adapter
is instantiated with its proved implementation. The independent original unary
source theorem is the sole explicit upstream input of this candidate module.
It is not obtained from the odd theorem: `oddProviderOfUnary` derives the latter
from this input and the actual physical original-graph source constructions. -/
namespace Paper2.PublicDichotomy
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.SourceFaithful
noncomputable section

/-- The native-X hardness clause with the original unary source input visible. -/
theorem native_hardness_of_unary (U : SourceFaithful.Paper1UnaryAccepted) (L : Language)
    (hnot : ¬ Tract (kImage L)) : Problem.SharpPHard .nativeX L := by
  let PO := Paper1Proved.OddResidue.oddProviderOfUnary
    Paper1Proved.directGadgetProvider Paper1Proved.restrictionProvider
    Paper1Proved.factorProvider U
  exact public_hardness_of_fixed_field .nativeX L
    (SourceFaithful.Synthesis.native_hardness_with_proved_local PO L hnot)

/-- The ordinary hardness clause is for the literal original graph input. -/
theorem ordinary_hardness_of_unary (U : SourceFaithful.Paper1UnaryAccepted) (L : Language)
    (hnot : ¬ Tract L.family) : Problem.SharpPHard .ordinary L := by
  let PO := Paper1Proved.OddResidue.oddProviderOfUnary
    Paper1Proved.directGadgetProvider Paper1Proved.restrictionProvider
    Paper1Proved.factorProvider U
  exact public_hardness_of_fixed_field .ordinary L
    (SourceFaithful.Synthesis.ordinary_hardness_with_proved_local PO L hnot)

/-- Both structural branches use the manuscript's strict exact output
convention and retain zero, nullary, duplicated and mixed-arity input rows. -/
theorem ordinary_dichotomy_of_unary (U : SourceFaithful.Paper1UnaryAccepted) (L : Language) :
    (Tract L.family ∧ Problem.InFP .ordinary L) ∨
      (¬ Tract L.family ∧ Problem.SharpPHard .ordinary L) := by
  classical
  by_cases ht : Tract L.family
  · exact Or.inl ⟨ht,TractableAlgorithms.ordinary_public_inFP_of_tract L ht⟩
  · exact Or.inr ⟨ht,ordinary_hardness_of_unary U L ht⟩

theorem native_dichotomy_of_unary (U : SourceFaithful.Paper1UnaryAccepted) (L : Language) :
    (Tract (kImage L) ∧ Problem.InFP .nativeX L) ∨
      (¬ Tract (kImage L) ∧ Problem.SharpPHard .nativeX L) := by
  classical
  by_cases ht : Tract (kImage L)
  · exact Or.inl ⟨ht,TractableAlgorithms.native_public_inFP_of_tract L ht⟩
  · exact Or.inr ⟨ht,native_hardness_of_unary U L ht⟩

/-- A single actual finite recognizer precedes every valid exact table list.
The evaluation and hardness implications are for each original language and
use its literal graph encoding; no recognition complexity bound is asserted. -/
theorem main_theorem_of_unary (U : SourceFaithful.Paper1UnaryAccepted) :
    ∃ r : TractRecognizer,
      (∀ raw : RawLanguage, ∀ hraw : raw.Valid,
        ∃ b : Bool, ∃ steps : ℕ,
          (fun c : Option r.machine.tm.Cfg => c.bind r.machine.tm.step)^[steps]
            (some (r.initial raw)) = some (r.final b) ∧
          r.machine.tm.step (r.final b) = none ∧
          (b = true ↔ Tract (Language.family ⟨raw,hraw⟩))) ∧
      (∀ L : Language,
        (r.decision L = true ↔ Tract L.family) ∧
        (Tract L.family → Problem.InFP .ordinary L) ∧
        (¬ Tract L.family → Problem.SharpPHard .ordinary L)) ∧
      (∀ L : Language,
        (Tract (kImage L) → Problem.InFP .nativeX L) ∧
        (¬ Tract (kImage L) → Problem.SharpPHard .nativeX L)) := by
  refine ⟨Paper1ProvedRecognition.recognizer,
    Paper1ProvedRecognition.recognizer.total_correct, ?_, ?_⟩
  · intro L
    exact ⟨Paper1ProvedRecognition.recognizer.correct L,
      TractableAlgorithms.ordinary_public_inFP_of_tract L,
      ordinary_hardness_of_unary U L⟩
  · intro L
    exact ⟨TractableAlgorithms.native_public_inFP_of_tract L,
      native_hardness_of_unary U L⟩

/-- Explicit branch form of the complete ordinary and native candidate,
sharing one original input language. The two structural alternatives are
disjoint; no separation between FP and #P-hardness is presumed. -/
theorem both_dichotomies_of_unary (U : SourceFaithful.Paper1UnaryAccepted) (L : Language) :
    ((Tract L.family ∧ Problem.InFP .ordinary L) ∨
      (¬ Tract L.family ∧ Problem.SharpPHard .ordinary L)) ∧
    ((Tract (kImage L) ∧ Problem.InFP .nativeX L) ∨
      (¬ Tract (kImage L) ∧ Problem.SharpPHard .nativeX L)) :=
  ⟨ordinary_dichotomy_of_unary U L,native_dichotomy_of_unary U L⟩

end
end Paper2.PublicDichotomy
