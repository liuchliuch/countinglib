import Paper2.PublicDichotomy
import Paper2.Paper1ProvedOddUnaryComplete

/-! The unconditional original-language public dichotomy. All structural
branches and accepted interfaces are instantiated with proved implementations,
including the independently proved original unary classification. The graph
inputs and returned outputs use the manuscript's literal strict conventions. -/
namespace Paper2.PublicDichotomy
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
noncomputable section

theorem native_hardness (L : Language) (hnot : ¬Tract (kImage L)) :
    Problem.SharpPHard .nativeX L :=
  native_hardness_of_unary Paper1Proved.OddUnary.UnaryProvider.proved L hnot

theorem ordinary_hardness (L : Language) (hnot : ¬Tract L.family) :
    Problem.SharpPHard .ordinary L :=
  ordinary_hardness_of_unary Paper1Proved.OddUnary.UnaryProvider.proved L hnot

theorem ordinary_dichotomy (L : Language) :
    (Tract L.family ∧ Problem.InFP .ordinary L) ∨
      (¬Tract L.family ∧ Problem.SharpPHard .ordinary L) :=
  ordinary_dichotomy_of_unary Paper1Proved.OddUnary.UnaryProvider.proved L

theorem native_dichotomy (L : Language) :
    (Tract (kImage L) ∧ Problem.InFP .nativeX L) ∨
      (¬Tract (kImage L) ∧ Problem.SharpPHard .nativeX L) :=
  native_dichotomy_of_unary Paper1Proved.OddUnary.UnaryProvider.proved L

/-- A single actual finite machine recognizes the source criterion. Every
language then has the proved polynomial evaluator and controlled hardness
implication for its own literal ordinary and native graph encoding. -/
theorem main_theorem :
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
        (¬Tract L.family → Problem.SharpPHard .ordinary L)) ∧
      (∀ L : Language,
        (Tract (kImage L) → Problem.InFP .nativeX L) ∧
        (¬Tract (kImage L) → Problem.SharpPHard .nativeX L)) :=
  main_theorem_of_unary Paper1Proved.OddUnary.UnaryProvider.proved

theorem both_dichotomies (L : Language) :
    ((Tract L.family ∧ Problem.InFP .ordinary L) ∨
      (¬Tract L.family ∧ Problem.SharpPHard .ordinary L)) ∧
    ((Tract (kImage L) ∧ Problem.InFP .nativeX L) ∨
      (¬Tract (kImage L) ∧ Problem.SharpPHard .nativeX L)) :=
  ⟨ordinary_dichotomy L,native_dichotomy L⟩

end
end Paper2.PublicDichotomy

