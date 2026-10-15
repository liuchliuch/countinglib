import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Calls
import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Run
import Counting.Algorithm.KarpLubyRequest.Sampling.TapeBounds

/-! # The complete group body calls the original sample algorithm -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open FixedFieldMachines BinaryCompose
open Counting.Algorithm.KarpLuby
open Counting.Algorithm.KarpLubyMachine
set_option backward.isDefEq.respectTransparency false

/-- Each addend is charged to a particular physical phase of the caller. -/
def bodyTime (rowWord massWord sampleWord history result : List Bool) (innerTime : ℕ) : ℕ :=
  (2 * (rowWord.length + massWord.length + sampleWord.length + history.length) + 8) +
  (2 * (sampleWord.length + 1)) + (2 * (rowWord.length + massWord.length) + 7) + innerTime +
  (2 * (rowWord.length + massWord.length + result.length) + 6) + (result.length + 1) +
  (2 * (rowWord.length + massWord.length + sampleWord.length +
    ((Encoding.frame result).reverse ++ history).length) + 13)

/-- A compositional precursor to the closed original-algorithm theorem below.
The premises concern executions of the concrete SampleBody machine only. -/
theorem run_of_samples (rowWord massWord history input : List Bool) (samples : ℕ)
    (step : (ℕ × List Bool) → ℕ × List Bool) (time : (ℕ × List Bool) → ℕ)
    (hr : ∀ i < samples, Iteration.SourceRun SampleBody.machine
      ((SampleBody.stateEncoding rowWord massWord).encode (step^[i] (0, input)))
      ((SampleBody.stateEncoding rowWord massWord).encode (step (step^[i] (0, input))))
      (time (step^[i] (0, input)))) :
    RunsExactly computer.step
      (initList computer (word rowWord massWord (encodeNat samples) history input))
      (haltList computer (word rowWord massWord (encodeNat samples)
        ((Encoding.frame (encodeNat (step^[samples] (0, input)).1)).reverse ++ history)
        (step^[samples] (0, input)).2))
      (bodyTime rowWord massWord (encodeNat samples) history (encodeNat (step^[samples] (0, input)).1)
        (Iteration.ticks (SampleBody.stateEncoding rowWord massWord) step time samples (0, input))) := by
  rw [init_word, halt_word]
  have hp := parse rowWord massWord (encodeNat samples) history input
  have hc := copy_samples input (fields rowWord massWord (encodeNat samples) history [] []) rfl
  have hsample : fields rowWord massWord (encodeNat samples) history [] [] 2 =
      encodeNat samples := rfl
  rw [hsample] at hc
  have hi := prepare_inner rowWord massWord (encodeNat samples) history input
  have hl := loop_call (SampleBody.stateEncoding rowWord massWord) step time samples (0, input)
    (fields [] [] (encodeNat samples) history [] []) hr
  have he := extract_result rowWord massWord (encodeNat samples) history
    (encodeNat (step^[samples] (0, input)).1) (step^[samples] (0, input)).2
  have ha := append_result rowWord massWord (encodeNat samples) history
    (encodeNat (step^[samples] (0, input)).1) (step^[samples] (0, input)).2
  have hs := serialize rowWord massWord (encodeNat samples)
    ((Encoding.frame (encodeNat (step^[samples] (0, input)).1)).reverse ++ history)
    (step^[samples] (0, input)).2
  convert (((((hp.trans hc).trans hi).trans hl).trans he).trans ha).trans hs using 1 <;>
    first | rfl | (dsimp only [bodyTime]; omega)

/-- The fourth field is already a physical reversed frame stream. It is not
decoded into a list of naturals, nor does its list length enter finite control. -/
def stateEncoding (rowWord massWord sampleWord : List Bool) :
    Computability.Encoding (List Bool × List Bool) Bool where
  encode state := word rowWord massWord sampleWord state.1 state.2
  decode input := do
    let (_, rest) ← Encoding.unframe input
    let (_, rest) ← Encoding.unframe rest
    let (_, rest) ← Encoding.unframe rest
    return ← Encoding.unframe rest
  decode_encode state := by
    rcases state with ⟨history, randomWord⟩
    simp [word, List.append_assoc]

/-- The proof-side raw-state specification of one original group computation. -/
def step {n : ℕ} (cs : List (DNF.Clause n)) (samples width : ℕ)
    (state : List Bool × List Bool) : List Bool × List Bool :=
  let result := (TapeIterationSpec.sampleStep cs width)^[samples] (0, state.2)
  ((Encoding.frame (encodeNat result.1)).reverse ++ state.1, result.2)

def sourceTime (n : ℕ) (rows : List RowSemantics.Cells) (samples : ℕ)
    (state : List Bool × List Bool) : ℕ :=
  let rowWord := Dense.CellCodec.rows rows
  let massWord := encodeNat (TotalMass.rowSum rows)
  let sampleStep := TapeIterationSpec.sampleStep (rows.map (DenseNormalization.denote n)) massWord.length
  let result := sampleStep^[samples] (0, state.2)
  bodyTime rowWord massWord (encodeNat samples) state.1 (encodeNat result.1)
    (Iteration.ticks (SampleBody.stateEncoding rowWord massWord) sampleStep
      (SampleBody.sourceTime n rows) samples (0, state.2))

/-- Closed operational endpoint: the only domain assumptions are actual row
lengths and enough physical random bits. The repeated body is the already
constructed sample machine, and zero samples follows the actual EOF branch. -/
theorem source_run (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples : ℕ) (state : List Bool × List Bool)
    (havailable : samples * (encodeNat (TotalMass.rowSum rows)).length ≤ state.2.length) :
    Iteration.SourceRun machine
      ((stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
        (encodeNat samples)).encode state)
      ((stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
        (encodeNat samples)).encode
        (step (rows.map (DenseNormalization.denote n)) samples
          (encodeNat (TotalMass.rowSum rows)).length state))
      (sourceTime n rows samples state) := by
  apply run_of_samples (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))
    state.1 state.2 samples
    (TapeIterationSpec.sampleStep (rows.map (DenseNormalization.denote n))
      (encodeNat (TotalMass.rowSum rows)).length) (SampleBody.sourceTime n rows)
  intro i hi
  exact SampleBody.source_run n rows hlen _
    (TapeBounds.sample_tape_available _ samples _ i 0 state.2 hi havailable)

/-- Primitive instructions are measured on this same complete group program. -/
theorem bit_cost (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (samples : ℕ) (state : List Bool × List Bool)
    (havailable : samples * (encodeNat (TotalMass.rowSum rows)).length ≤ state.2.length) :
    (Primitive.run program (sourceTime n rows samples state)
      (some (initList computer ((stateEncoding (Dense.CellCodec.rows rows)
        (encodeNat (TotalMass.rowSum rows)) (encodeNat samples)).encode state)))).2 =
      some (haltList computer ((stateEncoding (Dense.CellCodec.rows rows)
        (encodeNat (TotalMass.rowSum rows)) (encodeNat samples)).encode
        (step (rows.map (DenseNormalization.denote n)) samples
          (encodeNat (TotalMass.rowSum rows)).length state))) ∧
    (Primitive.run program (sourceTime n rows samples state)
      (some (initList computer ((stateEncoding (Dense.CellCodec.rows rows)
        (encodeNat (TotalMass.rowSum rows)) (encodeNat samples)).encode state)))).1 ≤
        machine.primitiveBudget * sourceTime n rows samples state :=
  Primitive.execution_cost program machine.primitiveBudget machine.program_budget_le _ _ _
    (source_run n rows hlen samples state havailable)

end Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
