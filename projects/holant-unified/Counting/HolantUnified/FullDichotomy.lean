import Paper2.PublicNativeClassification

/-!
# Closed full Holant dichotomy in its original exact-output contract

Thin wrappers of the pinned full-dichotomy release. The recognizers precede the
varying exact language. Evaluator and reduction bounds remain fixed-language
bounds, and public answers remain strict minimal-polynomial root descriptors.
The imported source discharges every accepted interface internally.
-/

namespace Counting.HolantUnified.FullDichotomy

open Paper2 Paper2.Tractable Paper2.ExactInput Paper2.Problem

/-- Paper Theorem 1.1 with both ordinary and native-X effective recognizers.
The statement retains the actual terminating finite-machine executions and
all original-language evaluation and hardness clauses. -/
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
        (¬Tract (kImage L) → Problem.SharpPHard .nativeX L)) :=
  Paper2.PublicDichotomy.main_theorem_with_native_recognition

/-- Paper Theorem 9.2: closed effective classification of the original native-X
problem, using the full criterion on its K-image. -/
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
        (¬Tract (kImage L) → Problem.SharpPHard .nativeX L)) :=
  Paper2.PublicDichotomy.theorem_9_2

/-- The ordinary structural branches for one fixed exact language. Their
structural conditions are disjoint; no complexity-class separation is assumed. -/
theorem ordinary_dichotomy (L : Language) :
    (Tract L.family ∧ Problem.InFP .ordinary L) ∨
      (¬Tract L.family ∧ Problem.SharpPHard .ordinary L) :=
  Paper2.PublicDichotomy.ordinary_dichotomy L

/-- The native-X structural branches preserve the original input language and
apply the criterion to its K-image. -/
theorem native_dichotomy (L : Language) :
    (Tract (kImage L) ∧ Problem.InFP .nativeX L) ∨
      (¬Tract (kImage L) ∧ Problem.SharpPHard .nativeX L) :=
  Paper2.PublicDichotomy.native_dichotomy L

/-- Both original graph models classified for the same finite exact language. -/
theorem both_dichotomies (L : Language) :
    ((Tract L.family ∧ Problem.InFP .ordinary L) ∨
      (¬Tract L.family ∧ Problem.SharpPHard .ordinary L)) ∧
    ((Tract (kImage L) ∧ Problem.InFP .nativeX L) ∨
      (¬Tract (kImage L) ∧ Problem.SharpPHard .nativeX L)) :=
  Paper2.PublicDichotomy.both_dichotomies L

/-- Fixed-language ordinary evaluation by a polynomial-time finite machine,
returning a strict minimal-root descriptor of the original graph value. -/
theorem ordinary_inFP (L : Language) (h : Tract L.family) :
    Problem.InFP .ordinary L :=
  Paper2.TractableAlgorithms.ordinary_public_inFP_of_tract L h

/-- Fixed-language native-X evaluation with the same strict output convention. -/
theorem native_inFP (L : Language) (h : Tract (kImage L)) :
    Problem.InFP .nativeX L :=
  Paper2.TractableAlgorithms.native_public_inFP_of_tract L h

/-- Ordinary hardness retains nonvacuity and length-controlled oracle
reductions against every correct polynomial-length public answer convention. -/
theorem ordinary_hardness (L : Language) (h : ¬Tract L.family) :
    Problem.SharpPHard .ordinary L :=
  Paper2.PublicDichotomy.ordinary_hardness L h

/-- Native-X hardness retains the original graph inputs, strict public root
answers, and all length-controlled reduction obligations. -/
theorem native_hardness (L : Language) (h : ¬Tract (kImage L)) :
    Problem.SharpPHard .nativeX L :=
  Paper2.PublicDichotomy.native_hardness L h

end Counting.HolantUnified.FullDichotomy
