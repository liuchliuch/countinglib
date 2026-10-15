import Counting.Algorithm.KarpLubyRequest.Preparation.Serialization
import Counting.Algorithm.KarpLubyRequest.Preparation.Physical

/-! Actual tape transfer, four payload frames, branch tagging and full cleanup.
The cost depends on the incoming physical bank size, including retained raw
fields. The raw-entry theorem can therefore charge this stage by its real
prefix space bound. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

private theorem tagged_cleanup_bound {cost tagged original count : ℕ}
    (hc : cost ≤ tagged + count) (hg : tagged ≤ original + 1) :
    cost + 2 ≤ original + count + 3 := by omega

private theorem serialization_time_bound {header moved original word budget : ℕ}
    (hw : word ≤ original) (hs : moved ≤ original + (2 * word + 2) * budget)
    (hf : header ≤ 8 * moved + 12) :
    header + (2 * word + 2) ≤
      (2 * original + 2) + 8 * (original + (2 * original + 2) * budget) + 12 := by
  have hm := Nat.mul_le_mul_right budget
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hw) 2)
  omega

private theorem finishing_time_bound {tail head bound original final budget count : ℕ}
    (htail : tail ≤ final + count + 3) (hspace : final ≤ original + head * budget)
    (hhead : head ≤ bound) :
    tail + head ≤ bound + (original + bound * budget) + count + 3 := by
  have hm := Nat.mul_le_mul_right budget hhead
  omega

def serializationBound (n : ℕ) : ℕ :=
  (2 * n + 2) + 8 * (n + (2 * n + 2) * primitiveBudget) + 12

def finishBound (n : ℕ) : ℕ :=
  serializationBound n + (n + serializationBound n * primitiveBudget) + workCount + 3

theorem headerSteps_bound (bank : Stack → List Bool) :
    headerSteps bank ≤ 8 * stackSize bank + 12 := by
  have a := word_length_le bank (budgetOriginal 1)
  have b := word_length_le bank (budgetOriginal 0)
  have c := word_length_le bank (budgetOriginal 2)
  have d := word_length_le bank (formulaStacks 12)
  dsimp only [headerSteps]
  omega

theorem positive_finish_bound (memory : Memory) (bank : Stack → List Bool) :
    ∃ time, time ≤ stackSize bank + workCount + 3 ∧
      RunsExactly computer.step (cfg .positive memory bank)
        (finalConfiguration (true :: bank output)) time := by
  let tagged := Function.update bank output (true :: bank output)
  refine ⟨prefixCost tagged workCount + 2, ?_, positive_finish memory bank⟩
  have hc := prefixCost_bound tagged
  have hg := stackSize_update_le bank output (true :: bank output) 1 (by simp only [List.length_cons]; exact le_rfl)
  change stackSize tagged ≤ stackSize bank + 1 at hg
  exact tagged_cleanup_bound hc hg

theorem zero_finish_bound (memory : Memory) (bank : Stack → List Bool)
    (ho : bank output = []) :
    ∃ time, time ≤ stackSize bank + workCount + 3 ∧
      RunsExactly computer.step (cfg .zero memory bank) (finalConfiguration [false]) time := by
  let tagged := Function.update bank output [false]
  refine ⟨prefixCost tagged workCount + 2, ?_, zero_finish memory bank ho⟩
  have hc := prefixCost_bound tagged
  have hg := stackSize_update_le bank output [false] 1 (by rw [ho]; exact le_refl _)
  change stackSize tagged ≤ stackSize bank + 1 at hg
  exact tagged_cleanup_bound hc hg

def tapeMoved (bank : Stack → List Bool) : Stack → List Bool :=
  Function.update (Function.update bank (budgetOriginal 3) []) output (bank (budgetOriginal 3))

theorem tape_moved_output (bank : Stack → List Bool) :
    tapeMoved bank output = bank (budgetOriginal 3) := Function.update_self _ _ _

theorem tape_moved_other (bank : Stack → List Bool) (k : Stack)
    (ho : k ≠ output) (ht : k ≠ budgetOriginal 3) : tapeMoved bank k = bank k :=
  (Function.update_of_ne ho _ _).trans (Function.update_of_ne ht _ _)

theorem serialized_payload (bank : Stack → List Bool) :
    true :: fourEmitted (tapeMoved bank) output =
      payload (bank (formulaStacks 12)) (bank (budgetOriginal 2))
        (bank (budgetOriginal 0)) (bank (budgetOriginal 1)) (bank (budgetOriginal 3)) := by
  rw [four_frames_output, tape_moved_output]
  rw [tape_moved_other bank (formulaStacks 12) (by intro h; cases h) (by intro h; cases h),
    tape_moved_other bank (budgetOriginal 2) (by intro h; cases h) (by decide),
    tape_moved_other bank (budgetOriginal 0) (by intro h; cases h) (by decide),
    tape_moved_other bank (budgetOriginal 1) (by intro h; cases h) (by decide)]
  rfl

/-- The entire positive physical tail returns the exact agreed codec and a
clean halt. The input words may be arbitrary: canonicity is supplied only by
previous actual machine stages, and is not needed to serialize the bytes. -/
theorem positive_payload (memory : Memory) (bank : Stack → List Bool)
    (ho : bank output = []) (ht : bank scratch = []) :
    ∃ time, time ≤ finishBound (stackSize bank) ∧
      RunsExactly computer.step (cfg .tapeMove memory bank)
        (finalConfiguration (payload (bank (formulaStacks 12)) (bank (budgetOriginal 2))
          (bank (budgetOriginal 0)) (bank (budgetOriginal 1)) (bank (budgetOriginal 3)))) time := by
  have hm := move_into (budgetOriginal 3) output scratch
    (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    .tapeMove .tapeRestore (.emitMove 0)
    (by intro m t; rfl) (by intro m t; rfl) memory bank ho ht
  have he := four_frames memory (tapeMoved bank) (by
    rw [tape_moved_other bank scratch (by intro h; cases h) (by intro h; cases h)]; exact ht)
  have prefixRun := hm.trans he
  obtain ⟨endTime, endBound, endRun⟩ := positive_finish_bound memory (fourEmitted (tapeMoved bank))
  rw [serialized_payload] at endRun
  let preTime := headerSteps (tapeMoved bank) + (2 * (bank (budgetOriginal 3)).length + 2)
  have preBound : preTime ≤ serializationBound (stackSize bank) := by
    have hw := word_length_le bank (budgetOriginal 3)
    have hs := stored_bits (cfg .tapeMove memory bank) (cfg (.emitMove 0) memory (tapeMoved bank)) _ hm
    have hf := headerSteps_bound (tapeMoved bank)
    dsimp only [cfg] at hs
    exact serialization_time_bound hw hs hf
  have hp := stored_bits (cfg .tapeMove memory bank)
    (cfg .positive memory (fourEmitted (tapeMoved bank))) preTime prefixRun
  refine ⟨endTime + preTime, ?_, prefixRun.trans endRun⟩
  dsimp only [cfg] at hp
  exact finishing_time_bound endBound hp preBound

/-- The real tape-gate flag dispatch is charged separately from the complete
payload/zero routine. -/
theorem gate_true (memory : Memory) (bank : Stack → List Bool)
    (hv : memory.budget.1.1 = true) :
    RunsExactly computer.step (cfg .gated memory bank) (cfg .tapeMove memory bank) 1 := by
  apply runsExactly_one
  change some (TM2.stepAux (program .gated) (none, memory) bank) = _
  dsimp only [program, TM2.stepAux]
  rw [hv]
  rfl

theorem gate_false (memory : Memory) (bank : Stack → List Bool)
    (hv : memory.budget.1.1 = false) :
    RunsExactly computer.step (cfg .gated memory bank) (cfg .zero memory bank) 1 := by
  apply runsExactly_one
  change some (TM2.stepAux (program .gated) (none, memory) bank) = _
  dsimp only [program, TM2.stepAux]
  rw [hv]
  rfl

end
end Counting.Algorithm.KarpLubyRequest.Preparation
