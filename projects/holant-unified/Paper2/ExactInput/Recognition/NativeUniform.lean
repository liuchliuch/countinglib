import Paper2.ExactInput.Recognition.Uniform

/-! The exact machine contract for effective recognition in native-X
coordinates. The machine reads the original literal descriptor-list bits and
decides the ordinary criterion on the K-transformed whole family. Recognition
is effective; no polynomial bound in the varying table list is asserted. -/
namespace Paper2.Problem
open Paper2.ExactInput Paper2.Tractable Computability

/-- A uniform finite-alphabet recognizer for the native whole-family criterion.
No equality, prime-quaternary, or other source promise is part of its domain. -/
structure NativeTractRecognizer where
  decision : Language → Bool
  machine : Turing.TM2Computable Language.bits encodingBoolBool.encode decision
  finiteAlphabets : ∀ k, Fintype (machine.tm.Γ k)
  correct : ∀ L, decision L = true ↔ Tract (kImage L)

namespace NativeTractRecognizer

/-- Start the actual source machine on the original raw table-list encoding. -/
def initial (r : NativeTractRecognizer) (raw : RawLanguage) : r.machine.tm.Cfg :=
  Turing.initList r.machine.tm
    ((rawLanguageEncoding.encode raw).map r.machine.inputAlphabet.invFun)

/-- The final configuration contains precisely the encoded Boolean answer. -/
def final (r : NativeTractRecognizer) (b : Bool) : r.machine.tm.Cfg :=
  Turing.haltList r.machine.tm
    ((encodingBoolBool.encode b).map r.machine.outputAlphabet.invFun)

/-- Finite transition execution on every valid original native table list. -/
theorem halts_on_valid (r : NativeTractRecognizer) (raw : RawLanguage)
    (hraw : raw.Valid) :
    ∃ steps : ℕ,
      (fun c : Option r.machine.tm.Cfg => c.bind r.machine.tm.step)^[steps]
        (some (r.initial raw)) = some (r.final (r.decision ⟨raw,hraw⟩)) := by
  let run := r.machine.outputsFun ⟨raw,hraw⟩
  exact ⟨run.steps,run.evals_in_steps⟩

@[simp] theorem final_step (r : NativeTractRecognizer) (b : Bool) :
    r.machine.tm.step (r.final b) = none := rfl

/-- Every valid exact native input halts with the correct applicable side. -/
theorem total_correct (r : NativeTractRecognizer) (raw : RawLanguage)
    (hraw : raw.Valid) :
    ∃ b : Bool, ∃ steps : ℕ,
      (fun c : Option r.machine.tm.Cfg => c.bind r.machine.tm.step)^[steps]
        (some (r.initial raw)) = some (r.final b) ∧
      r.machine.tm.step (r.final b) = none ∧
      (b = true ↔ Tract (kImage (⟨raw,hraw⟩ : Language))) := by
  obtain ⟨n,hn⟩ := r.halts_on_valid raw hraw
  exact ⟨r.decision ⟨raw,hraw⟩,n,hn,r.final_step _,r.correct _⟩

/-- Rejection negates the full native whole-family criterion. -/
theorem rejects_iff_not_tract (r : NativeTractRecognizer) (L : Language) :
    r.decision L = false ↔ ¬Tract (kImage L) := by
  rw [←r.correct L]
  cases r.decision L <;> simp

/-- Equivalent original table families give the same classification decision,
including changes in root descriptors, table order, and repeated rows. -/
theorem decision_eq_of_family_eq (r : NativeTractRecognizer) (L M : Language)
    (h : L.family = M.family) : r.decision L = r.decision M := by
  have he : (r.decision L = true) ↔ r.decision M = true := by
    rw [r.correct,r.correct]
    change Tract (familyAction sourceKBasis L.family) ↔
      Tract (familyAction sourceKBasis M.family)
    rw [h]
  cases hL : r.decision L <;> cases hM : r.decision M <;> simp_all

end NativeTractRecognizer
end Paper2.Problem

