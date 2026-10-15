import Counting.Algorithm.KarpLubyRequest.Embedded
import Counting.Algorithm.KarpLubyRequest.Contract
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-!
# Framed bit loops in an existing caller bank

These are bank-shape lemmas for the canonical extractor and emitter. They do
not define another machine or change the physical instruction count.
-/
namespace Counting.Algorithm.KarpLubyRequest.BankProtocol
open Turing Holant.Complexity StackProtocol GraphPreprocessing FixedFieldMachines
open Counting.Algorithm.KarpLuby
variable {K Λ τ : Type} [DecidableEq K]

theorem extract_into (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (hdt : dst ≠ tmp) (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (scan restore next bad : Λ)
    (hs : ExecutesAt step scan (Frame.scanStmt src tmp scan restore bad))
    (hr : ExecutesAt step restore (copyMoveStmt tmp dst restore next))
    (memory : τ) (bank : K → List Bool) (word suffix : List Bool)
    (hsrc : bank src = Encoding.frame word ++ suffix)
    (hd : bank dst = []) (ht : bank tmp = []) :
    RunsExactly step (cfg scan memory bank)
      (cfg next memory (Function.update (Function.update bank src suffix) dst word))
      (2 * (word.length + 1)) := by
  have h := Frame.extract_exact src dst tmp hsd hst hdt step scan restore next bad
    hs hr memory bank word suffix []
  rw [← Contract.frame_eq] at h
  have a : tapes3 bank src dst tmp (Encoding.frame word ++ suffix) [] [] = bank := by
    clear hs hr h
    funext k
    by_cases h0 : k = src <;> by_cases h1 : k = dst <;> by_cases h2 : k = tmp <;>
      simp_all [tapes3, Function.update_apply]
  have b : tapes3 bank src dst tmp suffix word [] =
      Function.update (Function.update bank src suffix) dst word := by
    clear hs hr h
    funext k
    by_cases h0 : k = src <;> by_cases h1 : k = dst <;> by_cases h2 : k = tmp <;>
      simp_all [tapes3, Function.update_apply]
  simpa only [List.append_nil, a, b] using h

theorem prepend_into (src dst tmp : K) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (hdt : dst ≠ tmp) (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (move delimiter emit next : Λ)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move delimiter))
    (hd : ExecutesAt step delimiter (FrameEmit.delimiterStmt dst emit))
    (he : ExecutesAt step emit (FrameEmit.emitStmt tmp dst emit next))
    (memory : τ) (bank : K → List Bool) (ht : bank tmp = []) :
    RunsExactly step (cfg move memory bank)
      (cfg next memory (Function.update (Function.update bank src []) dst
        (Encoding.frame (bank src) ++ bank dst))) (2 * (bank src).length + 3) := by
  have h := FrameEmit.prepend_exact src dst tmp hsd hst hdt step move delimiter emit next
    hm hd he memory bank (bank src) (bank dst)
  rw [← Contract.frame_eq] at h
  have a : tapes3 bank src dst tmp (bank src) (bank dst) [] = bank := by
    clear hm hd he h
    funext k
    by_cases h0 : k = src <;> by_cases h1 : k = dst <;> by_cases h2 : k = tmp <;>
      simp_all [tapes3, Function.update_apply]
  have b : tapes3 bank src dst tmp [] (Encoding.frame (bank src) ++ bank dst) [] =
      Function.update (Function.update bank src []) dst
        (Encoding.frame (bank src) ++ bank dst) := by
    clear hm hd he h
    funext k
    by_cases h0 : k = src <;> by_cases h1 : k = dst <;> by_cases h2 : k = tmp <;>
      simp_all [tapes3, Function.update_apply]
  simpa only [a, b] using h

end Counting.Algorithm.KarpLubyRequest.BankProtocol
