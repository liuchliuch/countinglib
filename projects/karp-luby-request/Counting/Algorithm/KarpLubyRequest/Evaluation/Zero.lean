import Counting.Algorithm.KarpLubyRequest.Evaluation.Bank

/-! The zero-result tag performs a real constant-sized literal serialization. -/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

theorem input_empty : (inputData []).tapes = fun _ => [] := by
  funext j
  rcases j with j | (j | (j | j))
  · change wordTape _ [] j = []
    simp only [wordTape, Function.update_apply, ite_self]
  all_goals rfl

theorem output_zero_word : Encoding.encodeOutput 0 =
    [true,true,true,false,true,false,false,true] := rfl

theorem zero_dispatch :
    computer.step (initList computer [false]) =
      some (configuration .zero initial (inputData [])) := by
  rw [input_eq]
  change some (⟨some Label.zero, initial,
    Function.update (inputData [false]).tapes random []⟩ : computer.Cfg) = _
  congr 2
  funext k
  rcases k with k | (k | (k | k))
  · by_cases hk : k = Iteration.bodyStack Sampling.GroupBody.machine Sampling.GroupBody.random
    · subst k; rfl
    · have ho : outerStacks k ≠ random := fun h => hk (outerStacks.injective h)
      change Function.update (inputData [false]).tapes random [] (outerStacks k) = _
      rw [Function.update_of_ne ho]
      exact (wordTape_other _ _ [false] hk).trans (wordTape_other _ _ [] hk).symm
  all_goals rfl

theorem zero_literal :
    computer.step (configuration .zero initial (inputData [])) =
      some (haltList computer (Encoding.encodeOutput 0)) := by
  rw [output_zero_word]
  change some (TM2.stepAux zeroStmt initial (inputData []).tapes) = _
  rw [input_empty, Machine.halt_eq]
  dsimp only [zeroStmt, TM2.stepAux]
  simp only [Function.update_self, Function.update_idem]
  rfl

/-- The tag is consumed in the first transition and the eight actual bit
pushes, state reset and halt are executed in the second. -/
theorem zero_run : RunsExactly computer.step (initList computer [false])
    (haltList computer (Encoding.encodeOutput 0)) 2 :=
  (runsExactly_one zero_dispatch).trans (runsExactly_one zero_literal)

end Counting.Algorithm.KarpLubyRequest.Evaluation
