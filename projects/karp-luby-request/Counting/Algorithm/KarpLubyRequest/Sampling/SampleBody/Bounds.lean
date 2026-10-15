import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Run
import Counting.Algorithm.KarpLubyRequest.Sampling.TrialBounds

/-! # Bit costs for the same serialized sample program -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

set_option backward.isDefEq.respectTransparency false

theorem statement_budget (label : Label) : TM2Cost.budget (program label) ≤ 9 := by
  cases label with
  | trial l =>
    change TM2Cost.budget (Embedded.block _ _ _ _) ≤ _
    rw [Embedded.statement_budget]
    exact Trial.statement_budget l
  | add l =>
    change TM2Cost.budget (MachineCall.block _ _ _ _ _) ≤ _
    rw [MachineCall.budget]
    exact (BinaryArithmetic.Addition.program_budget l).trans (by decide)
  | scan i => change (8 : ℕ) ≤ 9; decide
  | restore i => change (5 : ℕ) ≤ 9; decide
  | move i => change (5 : ℕ) ≤ 9; decide
  | delimiter i => change (2 : ℕ) ≤ 9; decide
  | emit i => change (6 : ℕ) ≤ 9; decide
  | done | bad => change (2 : ℕ) ≤ 9; decide

theorem bodyTime_le (rows mass : List Bool) (a b trialTime : ℕ) :
    bodyTime rows mass a b trialTime ≤ trialTime + 4 * rows.length + 4 * mass.length +
      6 * (encodeNat a).length + 4 * (encodeNat b).length + 21 := by
  have hs := sum_length_le a b
  have hm : max (encodeNat a).length (encodeNat b).length ≤
      (encodeNat a).length + (encodeNat b).length := by omega
  unfold bodyTime additionTime
  omega

theorem numerator_length_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (r : ℕ) :
    (encodeNat (Program.trial (rows.map (DenseNormalization.denote n)) r)).length ≤
      (encodeNat (TotalMass.rowSum rows)).length + 1 := by
  rw [← TrialSpec.trialValue_original n rows r hlen]
  unfold TrialSpec.trialValue
  split_ifs
  · rw [← RowMass.power_word, List.length_append, List.length_replicate]
    simp
  · change 0 ≤ _
    omega

/-- The unread suffix is retained without being scanned by the sample body. -/
theorem sourceTime_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (state : ℕ × List Bool) :
    sourceTime n rows state ≤
      220 * ((Dense.CellCodec.rows rows).length + 2 * (encodeNat (TotalMass.rowSum rows)).length + 1)^2 +
        4 * (Dense.CellCodec.rows rows).length + 8 * (encodeNat (TotalMass.rowSum rows)).length +
          6 * (encodeNat state.1).length + 25 := by
  let mass := encodeNat (TotalMass.rowSum rows)
  let bits := state.2.take mass.length
  let suffix := state.2.drop mass.length
  let b := Program.trial (rows.map (DenseNormalization.denote n)) (TapeIterationSpec.tapeValue bits)
  have hb : (encodeNat b).length ≤ mass.length + 1 := numerator_length_le n rows hlen _
  have hr : (encodeNat (BinaryArithmetic.value bits.reverse)).length ≤ mass.length :=
    (Trial.rank_length bits).trans (List.length_take_le _ _)
  have ht : Trial.runTime rows mass bits suffix ≤
      220 * ((Dense.CellCodec.rows rows).length + 2 * mass.length + 1)^2 := by
    refine (TrialBounds.prefix_selected_time_bound n rows mass suffix _ hlen).trans ?_
    exact Nat.mul_le_mul_left 220 (Nat.pow_le_pow_left (by omega) 2)
  have ho := bodyTime_le (Dense.CellCodec.rows rows) mass state.1 b (Trial.runTime rows mass bits suffix)
  change bodyTime (Dense.CellCodec.rows rows) mass state.1 b (Trial.runTime rows mass bits suffix) ≤ _
  change _ ≤ 220 * ((Dense.CellCodec.rows rows).length + 2 * mass.length + 1)^2 +
    4 * (Dense.CellCodec.rows rows).length + 8 * mass.length + 6 * (encodeNat state.1).length + 25
  omega

theorem word_length (rows mass acc tape : List Bool) :
    (word rows mass acc tape).length = 2 * (rows.length + mass.length + acc.length) + 3 + tape.length := by
  simp only [word, List.length_append, Encoding.frame_length]
  omega

/-- Measured instructions execute this same program, with no evaluator opcode. -/
theorem primitive_run (n : ℕ) (rows : List RowSemantics.Cells)
    (hlen : ∀ row ∈ rows, row.length = n) (state : ℕ × List Bool)
    (havailable : (encodeNat (TotalMass.rowSum rows)).length ≤ state.2.length) :
    (Primitive.run program (sourceTime n rows state)
      (some (initList computer
        ((stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))).encode state)))).2 =
      some (haltList computer
        ((stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))).encode
          (TapeIterationSpec.sampleStep (rows.map (DenseNormalization.denote n))
            (encodeNat (TotalMass.rowSum rows)).length state))) ∧
    (Primitive.run program (sourceTime n rows state)
      (some (initList computer
        ((stateEncoding (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows))).encode state)))).1 ≤
      9 * sourceTime n rows state :=
  Primitive.execution_cost program 9 statement_budget _ _ _ (source_run n rows hlen state havailable)

end Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
