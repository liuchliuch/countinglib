import Counting.Algorithm.KarpLubyRequest.Whole.Run
import Counting.Algorithm.KarpLubyRequest.Whole.Length

/-!
# Composing the actual preparation and evaluation costs

The preparation's executed-push bound controls the complete intermediate word.
The positive tape gate bounds numeric sample/group counts by that same word.
Thus a polynomial preparation certificate yields a polynomial for the actual
single composed source, including its physical handoff and zero branch.
-/
namespace Counting.Algorithm.KarpLubyRequest.Whole
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose Polynomial
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

def composedPolynomial (p : Polynomial ℕ) : Polynomial ℕ :=
  p + C 2 * (outputSizePolynomial p + 1) +
    Evaluation.costPolynomial.comp (outputSizePolynomial p) + C 2

theorem composedPolynomial_eval (p : Polynomial ℕ) (N : ℕ) :
    (composedPolynomial p).eval N = p.eval N +
      2 * ((outputSizePolynomial p).eval N + 1) +
      Evaluation.costPolynomial.eval ((outputSizePolynomial p).eval N) + 2 := by
  simp only [composedPolynomial, eval_add, eval_mul, eval_C, eval_one, eval_comp]

/-- Every premise about preparation below describes the same executed finite
source. The final raw theorem supplies this execution and its polynomial bound. -/
theorem run_bounded_of_preparation (p : Polynomial ℕ) (raw : List Bool)
    (prepareTime : ℕ) (ht : prepareTime ≤ p.eval raw.length)
    (hp : RunsExactly Preparation.computer.step (initList Preparation.computer raw)
      (Preparation.finalConfiguration (Preparation.rawResult raw)) prepareTime) :
    ∃ time, time ≤ (composedPolynomial p).eval raw.length ∧
      RunsExactly computer.step (initList computer raw)
        (haltList computer (ProgramEncoding.evalBits raw)) time := by
  have hsize := prepared_output_length_le_polynomial raw (Preparation.rawResult raw)
    prepareTime p hp ht
  rcases Preparation.rawResult_classification raw with ⟨hz, hv⟩ |
    ⟨r, hd, hvalid, hmass, hlen, hresult⟩
  · rw [hz] at hp hsize
    have run := compose_run raw [false] _ prepareTime 2 hp Evaluation.zero_run
    rw [← hv] at run
    refine ⟨_, ?_, run⟩
    rw [composedPolynomial_eval]
    simp only [List.length_cons, List.length_nil] at hsize ⊢
    omega
  · let rows := ValueBridge.originalRows r
    let s := Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon
    let g := Program.requestedGroups r.delta
    let middle := Preparation.payload (Dense.CellCodec.rows rows)
      (encodeNat (Sampling.TotalMass.rowSum rows)) (encodeNat s) (encodeNat g) r.tape
    have he : Preparation.rawResult raw = middle := by
      dsimp only [middle, rows, s, g]
      rw [ValueBridge.originalRows_mass]
      exact hresult
    rw [he] at hp hsize
    obtain ⟨hr, hw, ha, hb, htail⟩ := payload_fields_le (Dense.CellCodec.rows rows)
      (encodeNat (Sampling.TotalMass.rowSum rows)) (encodeNat s) (encodeNat g) r.tape
    obtain ⟨hs, hg⟩ := ValueBridge.requestedCounts_le_tape r hmass hlen
    have htail' : r.tape.length ≤ (outputSizePolynomial p).eval raw.length := htail.trans hsize
    have cost := Evaluation.timeBound_le_polynomial r.problem.variableCount rows
      (ValueBridge.originalRows_lengths r) s g r.tape ((outputSizePolynomial p).eval raw.length)
      (hr.trans hsize) (hw.trans hsize) (ha.trans hsize) (hs.trans htail')
      (hg.trans htail') (hb.trans hsize) htail'
    obtain ⟨time, bound, run⟩ := accepted_run raw r.problem.variableCount rows
      (ValueBridge.originalRows_lengths r) s g r.tape (ValueBridge.originalRows_tape r hlen)
      prepareTime hp
    rw [ValueBridge.output_eq_evalBits raw r hd hvalid hlen] at run
    refine ⟨time, ?_, run⟩
    rw [composedPolynomial_eval]
    change time ≤ Evaluation.timeBound r.problem.variableCount rows s g r.tape +
      (2 * (middle.length + 1) + prepareTime) at bound
    omega

end
end Counting.Algorithm.KarpLubyRequest.Whole

