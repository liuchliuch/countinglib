import Counting.Algorithm.KarpLubyRequest.Median.Program

/-! Exact source-level calls used by the nested median loops. -/
namespace Counting.Algorithm.KarpLubyRequest.Median.Program
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

theorem copy_run (j : CopyJob) (m : Memory) (t : Stack → List Bool)
    (hd : t (copyDst j) = []) (ht : t .temp = []) :
    RunsExactly computer.step (cfg (.copyMove j) m t)
      (cfg (copyNext j) m (Function.update t (copyDst j) (t (copySrc j))))
      (2 * (t (copySrc j)).length + 2) :=
  Embedded.copy_into (copySrc j) (copyDst j) .temp
    (by cases j <;> decide) (by cases j <;> decide) (by cases j <;> decide)
    computer.step (.copyMove j) (.copyRestore j) (copyNext j)
    (by intro s t; rfl) (by intro s t; rfl) m t hd ht

theorem clear_run (j : ClearJob) (m : Memory) (t : Stack → List Bool) :
    RunsExactly computer.step (cfg (.clear j) m t)
      (cfg (clearNext j) m (Function.update t (clearStack j) []))
      ((t (clearStack j)).length + 1) :=
  clear_exact computer.step (clearStack j) (.clear j) (clearNext j)
    (by intro s t; rfl) m t

theorem frame_run (j : FrameJob) (m : Memory) (t : Stack → List Bool)
    (word suffix : List Bool) (hs : t (frameSrc j) = Encoding.frame word ++ suffix)
    (hd : t (frameDst j) = []) (ht : t .temp = []) :
    RunsExactly computer.step (cfg (.scan j) m t)
      (cfg (frameNext j) m (Function.update (Function.update t (frameSrc j) suffix) (frameDst j) word))
      (2 * (word.length + 1)) := by
  have hsd : frameSrc j ≠ frameDst j := by cases j <;> decide
  have hst : frameSrc j ≠ Stack.temp := by cases j <;> decide
  have hdt : frameDst j ≠ Stack.temp := by cases j <;> decide
  have a : tapes3 t (frameSrc j) (frameDst j) .temp
      (Holant.Algebraic.frame word ++ suffix) [] [] = t := by
    rw [← Contract.frame_eq, ← hs]
    funext k
    by_cases h0 : k = frameSrc j <;> by_cases h1 : k = frameDst j <;>
      by_cases h2 : k = Stack.temp <;> simp_all [tapes3, Function.update_apply]
  have b : tapes3 t (frameSrc j) (frameDst j) .temp suffix (word ++ []) [] =
      Function.update (Function.update t (frameSrc j) suffix) (frameDst j) word := by
    simp only [List.append_nil, tapes3]
    funext k
    by_cases hk : k = .temp
    · subst k
      simp [Function.update_apply, Ne.symm hst, Ne.symm hdt, ht]
    · simp only [Function.update_apply, hk, ite_false]
  have hr := Frame.extract_exact (frameSrc j) (frameDst j) .temp hsd hst hdt
    computer.step (.scan j) (.restore j) (frameNext j) .bad
    (by intro s t; rfl) (by intro s t; rfl) m t word suffix []
  simpa only [a, b] using hr

def comparisonTapes (t : Stack → List Bool) (left right answer : List Bool) : Stack → List Bool :=
  Function.update (Function.update (Function.update (Function.update t .left left)
    .right right) .work []) .answer answer

theorem comparison_run (minimum selected eligible : Bool) (t : Stack → List Bool) (a b : ℕ) :
    RunsExactly computer.step
      (cfg (.compare minimum) (memory selected eligible)
        (comparisonTapes t (encodeNat a) (encodeNat b) []))
      (cfg (compareReturn minimum) (memory selected eligible)
        (comparisonTapes t [] [] [decide (a < b)]))
      (max (encodeNat a).length (encodeNat b).length + 1) := by
  let first := BinaryArithmetic.Comparison.cfg (some ()) false (encodeNat a) (encodeNat b) []
  let lastSource := BinaryArithmetic.Comparison.cfg none false [] [] [decide (a < b)]
  have sourceRun := BinaryArithmetic.Comparison.compute_encodeNat_exact a b
  have adapted := StateAdapter.run comparisonState BinaryArithmetic.Comparison.computer.m
    (none, (selected, eligible)) first lastSource _ sourceRun
  have code : ∀ l, program (compareLabel minimum l) =
      Embedded.block comparisonMap (compareLabel minimum) (compareReturn minimum)
        ((StateAdapter.program comparisonState BinaryArithmetic.Comparison.computer.m) l) := by
    intro l; cases l; rfl
  have hi : Embedded.Rel comparisonMap (compareLabel minimum) (compareReturn minimum) t
      (StateAdapter.cfg comparisonState (none, (selected, eligible)) first)
      (cfg (.compare minimum) (memory selected eligible)
        (comparisonTapes t (encodeNat a) (encodeNat b) [])) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; cases k <;> rfl
    · intro j hj
      cases j with
      | left => exact False.elim (hj .left rfl)
      | right => exact False.elim (hj .right rfl)
      | work => exact False.elim (hj .work rfl)
      | answer => exact False.elim (hj .out rfl)
      | _ => rfl
  obtain ⟨last, run, hrel⟩ := Embedded.run comparisonMap (compareLabel minimum) (compareReturn minimum)
    (StateAdapter.program comparisonState BinaryArithmetic.Comparison.computer.m) program code
    _ _ _ t _ hi adapted
  have htape : last.stk = comparisonTapes t [] [] [decide (a < b)] := by
    funext k
    cases k with
    | left => exact hrel.2.2.1 BinaryArithmetic.Addition.Stack.left
    | right => exact hrel.2.2.1 BinaryArithmetic.Addition.Stack.right
    | work => exact hrel.2.2.1 BinaryArithmetic.Addition.Stack.work
    | answer => exact hrel.2.2.1 BinaryArithmetic.Addition.Stack.out
    | _ =>
      exact hrel.2.2.2 _ (by intro j; cases j <;> decide)
  have he : last = cfg (compareReturn minimum) (memory selected eligible)
      (comparisonTapes t [] [] [decide (a < b)]) := by
    rcases last with ⟨label, state, tape⟩
    have hlab := hrel.1
    have hstate := hrel.2.1
    change label = some (compareReturn minimum) at hlab
    change state = (none, memory selected eligible) at hstate
    change tape = comparisonTapes t [] [] [decide (a < b)] at htape
    subst label state tape
    rfl
  change RunsExactly computer.step _ _ _ at run
  exact he ▸ run

end Counting.Algorithm.KarpLubyRequest.Median.Program
