import Counting.Algorithm.KarpLubyRequest.Preparation.Calls
import Counting.Algorithm.KarpLubyRequest.Preparation.Transfers
import Counting.Algorithm.KarpLubyRequest.Preparation.BankUpdates

/-! Dense rows are copied, then consumed by the real mass machine. The original
row stream remains available to the sampler and serializer. Zero mass is tested
by its actual canonical empty word before any sample/group arithmetic. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
set_option backward.isDefEq.respectTransparency false

def massData (d : Data) (rows : List Sampling.RowSemantics.Cells) : Data :=
  {d with mass := Sampling.TotalMass.tapes [] [] (encodeNat (Sampling.TotalMass.rowSum rows)) [] [] []}

theorem mass_after_dense (d : Data) (memory : Memory)
    (rows : List Sampling.RowSemantics.Cells)
    (hf : d.formula 12 = Dense.CellCodec.rows rows)
    (hm : d.mass = fun _ => []) (ht : d.scratch = []) :
    RunsExactly computer.step
      (configuration (.copyMove .rows) (none, {memory with mass := BinaryArithmetic.Addition.initial}) d)
      (configuration .massCheck (none, {memory with mass := BinaryArithmetic.Addition.initial})
        (massData d rows))
      (2 * (Dense.CellCodec.rows rows).length + 2 + Sampling.TotalMass.runTime rows 0) := by
  have hd : d.tapes (copyDestination .rows) = [] := by
    change d.mass 0 = []; rw [hm]
  have hc := copy_run .rows {memory with mass := BinaryArithmetic.Addition.initial} d.tapes hd ht
  change RunsExactly computer.step _
    (cfg (.mass 0) _ (Function.update d.tapes (massStacks 0) (d.formula 12)))
    (2 * (d.formula 12).length + 2) at hc
  rw [hf, update_mass] at hc
  have he : Function.update d.mass 0 (Dense.CellCodec.rows rows) =
      Sampling.TotalMass.tapes (Dense.CellCodec.rows rows) [] [] [] [] [] := by
    rw [hm]
    funext k; fin_cases k <;> rfl
  rw [he] at hc
  convert hc.trans (mass_call d memory rows) using 1 <;> first | rfl | omega

theorem mass_empty_branch (memory : Memory) (bank : Stack → List Bool)
    (hm : bank (massStacks 2) = []) :
    RunsExactly computer.step (cfg .massCheck memory bank) (cfg .zero memory bank) 1 := by
  apply runsExactly_one
  change some (TM2.stepAux (program .massCheck) (none, memory) bank) = _
  dsimp only [program, TM2.stepAux]
  rw [hm]
  rfl

theorem mass_nonempty_branch (memory : Memory) (bank : Stack → List Bool)
    (hm : bank (massStacks 2) ≠ []) :
    RunsExactly computer.step (cfg .massCheck memory bank)
      (cfg (.copyMove .clauses) memory bank) 1 := by
  apply runsExactly_one
  change some (TM2.stepAux (program .massCheck) (none, memory) bank) = _
  dsimp only [program, TM2.stepAux]
  cases hw : bank (massStacks 2) with
  | nil => exact (hm hw).elim
  | cons b bs => rfl

end
end Counting.Algorithm.KarpLubyRequest.Preparation
