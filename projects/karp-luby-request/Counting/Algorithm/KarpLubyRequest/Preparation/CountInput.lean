import Counting.Algorithm.KarpLubyRequest.Preparation.DenseInput

/-! The normalized clause count is copied from its real dense-machine output
into the retained parameter caller. No semantic count is supplied to control. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
set_option backward.isDefEq.respectTransparency false

theorem count_bank_install (source : RequestParser.Stack → List Bool) (word : List Bool) :
    Function.update (validatedData source).counts ParameterCountsBank.clauses word =
      ParameterCountsBank.ready (ParameterValidation.prepared source 4) word [] := by
  funext k
  rcases k with k | (k | k)
  · rfl
  · fin_cases k <;> rfl
  · change [] = wordTape ParameterCountsBank.Arithmetic.input [] k
    simp only [wordTape, Function.update_apply, ite_self]

theorem count_input_copy (source : RequestParser.Stack → List Bool) (d : Data)
    (memory : Memory) (m : ℕ)
    (hc : d.counts = (validatedData source).counts)
    (hf : d.formula 4 = encodeNat m) (ht : d.scratch = []) :
    RunsExactly computer.step (configuration (.copyMove .clauses) (none, memory) d)
      (configuration (.counts (ParameterCountsBank.own 0)) (none, memory)
        {d with counts := (ParameterCountsBank.ready (ParameterValidation.prepared source 4)
          (encodeNat m) [])}) (2 * (encodeNat m).length + 2) := by
  have hd : d.tapes (copyDestination .clauses) = [] := by
    change d.counts ParameterCountsBank.clauses = []
    rw [hc]
    rfl
  have run := copy_run .clauses memory d.tapes hd ht
  change RunsExactly computer.step _
    (cfg (.counts (ParameterCountsBank.own 0)) memory
      (Function.update d.tapes (countsStacks ParameterCountsBank.clauses) (d.formula 4)))
    (2 * (d.formula 4).length + 2) at run
  rw [hf, update_counts, hc, count_bank_install] at run
  exact run

end
end Counting.Algorithm.KarpLubyRequest.Preparation
