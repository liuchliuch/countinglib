import Counting.Algorithm.KarpLubyRequest.Preparation.Rejection
import Counting.Algorithm.KarpLubyRequest.Evaluation.Run
import Holant.Complexity.BinaryCompose.Composition

/-!
# The single source program for the complete raw request

The existing sequential compiler embeds the preparation and evaluation source
programs in disjoint finite banks. Its two physical transfer loops consume the
entire intermediate word and preserve its order. Their cost is included below;
neither an encoder nor a semantic evaluator is installed as an instruction.
-/
namespace Counting.Algorithm.KarpLubyRequest.Whole
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing
open Counting.Algorithm.KarpLuby
open Sampling
set_option backward.isDefEq.respectTransparency false

/-- Both complete source programs and the original physical handoff compiler. -/
def machine : BinaryCompose.Machine := Preparation.machine.compose Evaluation.machine

abbrev computer := machine.computer

/-- The two independently stated payload codecs agree bit for bit. -/
theorem payload_eq (rows mass samples groups tape : List Bool) :
    Preparation.payload rows mass samples groups tape =
      Evaluation.payload rows mass samples groups tape := rfl

/-- The clean preparation endpoint is physically delivered to the evaluator.
The `2 * (middle.length + 1)` charge comes from the actual two transfer loops. -/
theorem compose_run (raw middle output : List Bool) (prepareTime evaluateTime : ℕ)
    (hp : RunsExactly Preparation.computer.step (initList Preparation.computer raw)
      (Preparation.finalConfiguration middle) prepareTime)
    (he : RunsExactly Evaluation.computer.step (initList Evaluation.computer middle)
      (haltList Evaluation.computer output) evaluateTime) :
    RunsExactly computer.step (initList computer raw) (haltList computer output)
      (evaluateTime + (2 * (middle.length + 1) + prepareTime)) := by
  rw [← Preparation.halt_eq] at hp
  exact Machine.compose_run Preparation.machine Evaluation.machine raw middle output
    prepareTime evaluateTime hp he

/-- Malformed requests and invalid accuracy/confidence parameters already have
a closed all-raw execution through the composed program and the literal output
serializer. This theorem makes no promise about the input word. -/
theorem rejected_run (raw : List Bool) (h : Preparation.parameterStatus raw = false) :
    ∃ time, time ≤ Preparation.rejectedBound raw.length + 6 ∧
      RunsExactly computer.step (initList computer raw)
        (haltList computer (ProgramEncoding.evalBits raw)) time := by
  obtain ⟨time, ht, hp⟩ := Preparation.rejected_run raw h
  have run := compose_run raw [false] (Encoding.encodeOutput 0) time 2 hp Evaluation.zero_run
  rw [← Preparation.rejected_value raw h] at run
  refine ⟨_, ?_, run⟩
  simp only [List.length_cons, List.length_nil]
  omega

/-- An actual accepted preparation execution is followed by the two materialized
sampling loops, median selection, normalization and exact original output codec.
The total all-raw theorem later supplies `hp` from the original decoder. -/
theorem accepted_run (raw : List Bool) (n : ℕ) (rows : List RowSemantics.Cells)
    (hrows : ∀ row ∈ rows, row.length = n) (s g : ℕ) (tape : List Bool)
    (hlen : tape.length = g * (s * (encodeNat (Sampling.TotalMass.rowSum rows)).length))
    (prepareTime : ℕ)
    (hp : RunsExactly Preparation.computer.step (initList Preparation.computer raw)
      (Preparation.finalConfiguration
        (Preparation.payload (Dense.CellCodec.rows rows)
          (encodeNat (Sampling.TotalMass.rowSum rows)) (encodeNat s) (encodeNat g) tape))
      prepareTime) :
    ∃ time, time ≤ Evaluation.timeBound n rows s g tape +
        (2 * ((Preparation.payload (Dense.CellCodec.rows rows)
          (encodeNat (Sampling.TotalMass.rowSum rows)) (encodeNat s) (encodeNat g) tape).length + 1)
          + prepareTime) ∧
      RunsExactly computer.step (initList computer raw)
        (haltList computer (Encoding.encodeOutput (Evaluation.resultValue n rows s g tape))) time := by
  obtain ⟨time, ht, he⟩ := Evaluation.prepared_run n rows hrows s g tape hlen
  have run := compose_run raw _ _ prepareTime time hp he
  exact ⟨_, Nat.add_le_add_right ht _, run⟩

/-- Primitive instrumentation is applied to this same integrated program. -/
theorem primitive_run (raw output : List Bool) (time : ℕ)
    (run : RunsExactly computer.step (initList computer raw) (haltList computer output) time) :
    (Primitive.run machine.program time (some (initList computer raw))).2 =
        some (haltList computer output) ∧
      (Primitive.run machine.program time (some (initList computer raw))).1 ≤
        machine.primitiveBudget * time :=
  Primitive.execution_cost machine.program machine.primitiveBudget machine.program_budget_le
    time _ _ run

end
end Counting.Algorithm.KarpLubyRequest.Whole

