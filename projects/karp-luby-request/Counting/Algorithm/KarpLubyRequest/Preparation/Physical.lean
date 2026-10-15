import Counting.Algorithm.KarpLubyRequest.Preparation.Transfers
import Counting.Algorithm.KarpLubyRequest.BankProtocol

/-! Moving and discarding framed words in the existing preparation bank.
These lemmas describe executed source loops with arbitrary untouched stacks. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

theorem tapes3_present (bank : Stack → List Bool) (src dst tmp : Stack) :
    tapes3 bank src dst tmp (bank src) (bank dst) (bank tmp) = bank := by
  dsimp only [tapes3]
  rw [Function.update_eq_self, Function.update_eq_self, Function.update_eq_self]

theorem tapes3_two (bank : Stack → List Bool) (src dst tmp : Stack)
    (hst : src ≠ tmp) (hdt : dst ≠ tmp) (a b : List Bool) :
    tapes3 bank src dst tmp a b (bank tmp) =
      Function.update (Function.update bank src a) dst b := by
  apply Function.update_eq_self_iff.mpr
  rw [Function.update_of_ne hdt.symm, Function.update_of_ne hst.symm]

theorem move_into (src dst tmp : Stack) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (hdt : dst ≠ tmp) (move restore next : Label)
    (hm : ExecutesAt computer.step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt computer.step restore (copyMoveStmt tmp dst restore next))
    (memory : Memory) (bank : Stack → List Bool)
    (hd : bank dst = []) (ht : bank tmp = []) :
    RunsExactly computer.step (cfg move memory bank)
      (cfg next memory (Function.update (Function.update bank src []) dst (bank src)))
      (2 * (bank src).length + 2) := by
  have h1 := copy_move_exact src dst tmp hsd hst computer.step move restore hm
    memory bank (bank src) [] []
  have h2 := Frame.restore_exact src dst tmp hdt computer.step restore next hr
    memory bank [] [] (bank src).reverse
  have ha : tapes3 bank src dst tmp (bank src) [] [] = bank := by
    simpa only [hd, ht] using tapes3_present bank src dst tmp
  have hz : tapes3 bank src dst tmp [] (bank src) [] =
      Function.update (Function.update bank src []) dst (bank src) := by
    simpa only [ht] using tapes3_two bank src dst tmp hst hdt [] (bank src)
  simp only [List.append_nil] at h1
  simp only [List.reverse_reverse, List.length_reverse, List.append_nil] at h2
  rw [ha] at h1
  rw [hz] at h2
  convert h1.trans h2 using 1 <;> omega

theorem drop_into (k : Fin 2) (memory : Memory) (bank : Stack → List Bool)
    (word rest : List Bool)
    (hsrc : bank countOutput = Encoding.frame word ++ rest) (ht : bank scratch = []) :
    RunsExactly computer.step (cfg (.dropScan k) memory bank)
      (cfg (dropNext k) memory (Function.update bank countOutput rest))
      (2 * word.length + 2) := by
  have h := drop_frame k memory bank word rest (bank output)
  rw [← Contract.frame_eq] at h
  have ha : tapes3 bank countOutput output scratch (Encoding.frame word ++ rest)
      (bank output) [] = bank := by
    rw [← hsrc, ← ht]
    exact tapes3_present bank countOutput output scratch
  have hz : tapes3 bank countOutput output scratch rest (bank output) [] =
      Function.update bank countOutput rest := by
    rw [← ht, tapes3_two bank countOutput output scratch
      (by intro h; cases h) (by intro h; cases h)]
    apply Function.update_eq_self_iff.mpr
    exact (Function.update_of_ne (show output ≠ countOutput by intro h; cases h) rest bank).symm
  simpa only [ha, hz] using h

end
end Counting.Algorithm.KarpLubyRequest.Preparation
