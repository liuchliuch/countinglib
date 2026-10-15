import Paper2.Paper1Accepted
import Paper2.Tractable.CriteriaFacts

/-!
# Uniform recognition of the main theorem's seven-clause predicate

The only imported algorithm is the already explicit Paper 1 Theorem 2.22
parameter. Its domain is every valid literal finite algebraic table list, not
one of the native equality/quaternary promise subtypes. The execution witnesses
below expose its finite TM2 transition runs on exactly `Language.bits`.

No classical decision procedure, effective validity test on malformed inputs,
polynomial recognition bound, or uniform K-table conversion is asserted.
-/
namespace Paper2.Problem.TractRecognizer
open Paper2.ExactInput Paper2.Tractable Computability

/-- Start the actual source machine on the literal raw table-list encoding. -/
def initial (r : TractRecognizer) (raw : RawLanguage) : r.machine.tm.Cfg :=
  Turing.initList r.machine.tm
    ((rawLanguageEncoding.encode raw).map r.machine.inputAlphabet.invFun)

/-- The final configuration contains precisely the encoded Boolean answer. -/
def final (r : TractRecognizer) (b : Bool) : r.machine.tm.Cfg :=
  Turing.haltList r.machine.tm
    ((encodingBoolBool.encode b).map r.machine.outputAlphabet.invFun)

/-- Literal finite transition count for every valid input, without a source
promise, arity bound, nonzeroness assumption, or supplied transform witness. -/
theorem halts_on_valid (r : TractRecognizer) (raw : RawLanguage)
    (hraw : raw.Valid) :
    ∃ steps : ℕ,
      (fun c : Option r.machine.tm.Cfg => c.bind r.machine.tm.step)^[steps]
        (some (r.initial raw)) = some (r.final (r.decision ⟨raw, hraw⟩)) := by
  let run := r.machine.outputsFun ⟨raw, hraw⟩
  exact ⟨run.steps, run.evals_in_steps⟩

/-- Reaching the displayed final configuration really halts the transition
machine; it is not merely reaching an arbitrary intermediate state. -/
@[simp] theorem final_step (r : TractRecognizer) (b : Bool) :
    r.machine.tm.step (r.final b) = none := rfl

/-- The exact seven-way disjunction, retaining all family-wide quantifiers. -/
theorem accepts_iff_seven_clauses (r : TractRecognizer) (L : Language) :
    r.decision L = true ↔
      OneSidedAlternative (preprocess L.family) ∨
      SingleWeightAlternative (preprocess L.family) ∨
      ArityTwoAlternative (preprocess L.family) ∨
      MatchingAlternative (preprocess L.family) ∨
      CommonTransformable affineClass (preprocess L.family) ∨
      CommonTransformable productClass (preprocess L.family) ∨
      CommonTransformable localAffineClass (preprocess L.family) :=
  (r.correct L).trans (tract_iff_core_of_finite L.family L.family_finite)

/-- Rejection negates the full criterion, not merely a chosen sufficient branch. -/
theorem rejects_iff_not_tract (r : TractRecognizer) (L : Language) :
    r.decision L = false ↔ ¬ Tract L.family := by
  rw [← r.correct L]
  cases r.decision L <;> simp

/-- Every valid descriptor list terminates with the mathematically correct
answer, including the false answer when all seven alternatives fail. -/
theorem total_correct (r : TractRecognizer) (raw : RawLanguage)
    (hraw : raw.Valid) :
    ∃ b : Bool, ∃ steps : ℕ,
      (fun c : Option r.machine.tm.Cfg => c.bind r.machine.tm.step)^[steps]
        (some (r.initial raw)) = some (r.final b) ∧
      r.machine.tm.step (r.final b) = none ∧
      (b = true ↔ Tract (Language.family ⟨raw, hraw⟩)) := by
  obtain ⟨n, hn⟩ := r.halts_on_valid raw hraw
  exact ⟨r.decision ⟨raw, hraw⟩, n, hn, r.final_step _, r.correct _⟩

/-- Recognition depends only on the denoted family. In particular, alternative
valid root rectangles, table order, and duplicate descriptors cannot change it
when they describe the same finite signature set. -/
theorem decision_eq_of_family_eq (r : TractRecognizer) (L M : Language)
    (h : L.family = M.family) : r.decision L = r.decision M := by
  have he : (r.decision L = true) ↔ r.decision M = true := by
    rw [r.correct, r.correct, h]
  cases hL : r.decision L <;> cases hM : r.decision M <;> simp_all

/-- The precise preprocessing convention changes classification only. It does
not delete zero vertices or scalar vertices from an evaluation instance. -/
theorem decision_eq_of_preprocess_eq (r : TractRecognizer) (L M : Language)
    (h : preprocess L.family = preprocess M.family) : r.decision L = r.decision M := by
  have he : (r.decision L = true) ↔ r.decision M = true := by
    rw [r.correct, r.correct]
    change (_ ∧ TractCore (preprocess L.family)) ↔
      (_ ∧ TractCore (preprocess M.family))
    rw [h]
  cases hL : r.decision L <;> cases hM : r.decision M <;> simp_all

end Paper2.Problem.TractRecognizer

namespace Paper2.ExactInput.Recognition
open Paper2.Problem Paper2.Tractable

/-- The recognition claim by itself depends only on the permitted recognition
input. In particular, it is independent of the output convention used for
Holant evaluation. The single finite-alphabet machine is chosen before every
valid raw descriptor list and runs on that list's literal encoding. -/
theorem uniform_recognition (h : Nonempty TractRecognizer) :
    ∃ r : TractRecognizer,
      ∀ raw : RawLanguage, ∀ hraw : raw.Valid,
        ∃ b : Bool, ∃ steps : ℕ,
          (fun c : Option r.machine.tm.Cfg => c.bind r.machine.tm.step)^[steps]
            (some (r.initial raw)) = some (r.final b) ∧
          r.machine.tm.step (r.final b) = none ∧
          (b = true ↔ Tract (Language.family ⟨raw, hraw⟩)) := by
  obtain ⟨r⟩ := h
  exact ⟨r, r.total_correct⟩

/-- Main-theorem recognition and the ordinary FP implication, uniformly over all
valid finite exact table lists. No native-source promise or new accepted field
is used. The one recognizer is chosen before the language quantifier. -/
theorem main_recognition_and_evaluation (P : Paper1Accepted) :
    ∃ r : TractRecognizer,
      (∀ raw : RawLanguage, ∀ hraw : raw.Valid,
        ∃ b : Bool, ∃ steps : ℕ,
          (fun c : Option r.machine.tm.Cfg => c.bind r.machine.tm.step)^[steps]
            (some (r.initial raw)) = some (r.final b) ∧
          r.machine.tm.step (r.final b) = none ∧
          (b = true ↔ Tract (Language.family ⟨raw, hraw⟩))) ∧
      (∀ L : Language, r.decision L = true → Problem.InFP .ordinary L) := by
  obtain ⟨r⟩ := P.recognition_2_22
  exact ⟨r, r.total_correct, fun L h => P.evaluation_2_22 L ((r.correct L).mp h)⟩

end Paper2.ExactInput.Recognition
