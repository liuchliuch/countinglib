import Counting.Algorithm.KarpLubyRequest.Evaluation.Bank

/-! Actual frame scans, count copies and emissions in the evaluator bank. -/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
open Turing Holant.Complexity StackProtocol GraphPreprocessing FixedFieldMachines
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

theorem header_extract (i : Fin 4) (memory : Memory) (bank : Stack → List Bool)
    (word suffix : List Bool) (hi : bank random = Encoding.frame word ++ suffix)
    (hd : bank (headerField i) = []) (ht : bank scratch = []) :
    RunsExactly computer.step (cfg (.scan i) memory bank)
      (cfg (headerNext i) memory
        (Function.update (Function.update bank random suffix) (headerField i) word))
      (2 * (word.length + 1)) := by
  apply BankProtocol.extract_into random (headerField i) scratch
    (by intro h; cases h) (by intro h; cases h) ?_ computer.step
    (.scan i) (.restore i) (headerNext i) .bad
    (by intro m t; rfl) (by intro m t; rfl) memory bank word suffix hi hd ht
  intro h
  have hv := congrArg (fun k : Stack => match k with
    | .inr (.inl j) => j.val | _ => 7) h
  change i.val = 5 at hv
  omega

theorem returned_extract (i : Fin 4) (memory : Memory) (bank : Stack → List Bool)
    (word suffix : List Bool) (hi : bank random = Encoding.frame word ++ suffix)
    (hd : bank (returnedField i) = []) (ht : bank scratch = []) :
    RunsExactly computer.step (cfg (.resultScan i) memory bank)
      (cfg (returnedNext i) memory
        (Function.update (Function.update bank random suffix) (returnedField i) word))
      (2 * (word.length + 1)) := by
  apply BankProtocol.extract_into random (returnedField i) scratch
    (by fin_cases i <;> intro h <;> cases h) (by intro h; cases h)
    (by fin_cases i <;> decide) computer.step
    (.resultScan i) (.resultRestore i) (returnedNext i) .bad
    (by intro m t; rfl) (by intro m t; rfl) memory bank word suffix hi hd ht

theorem header_emit (i : Fin 3) (memory : Memory) (bank : Stack → List Bool)
    (ht : bank scratch = []) :
    RunsExactly computer.step (cfg (.emitMove i) memory bank)
      (cfg (emitNext i) memory (Function.update (Function.update bank (emitField i) []) random
        (Encoding.frame (bank (emitField i)) ++ bank random)))
      (2 * (bank (emitField i)).length + 3) := by
  apply BankProtocol.prepend_into (emitField i) random scratch
    (by intro h; cases h) ?_ (by intro h; cases h) computer.step
    (.emitMove i) (.emitDelimiter i) (.emit i) (emitNext i)
    (by intro m t; rfl) (by intro m t; rfl) (by intro m t; rfl) memory bank ht
  intro h
  have hv := congrArg (fun k : Stack => match k with
    | .inr (.inl j) => j.val | _ => 7) h
  change 2-i.val = 5 at hv
  omega

theorem count_copy (memory : Memory) (bank : Stack → List Bool)
    (hc : bank counter = []) (ht : bank scratch = []) :
    RunsExactly computer.step (cfg .countMove memory bank)
      (cfg .groupZero memory (Function.update bank counter (bank groups)))
      (2 * (bank groups).length + 2) :=
  Embedded.copy_into groups counter scratch (by intro h; cases h) (by decide)
    (by intro h; cases h) computer.step .countMove .countRestore .groupZero
    (by intro m t; rfl) (by intro m t; rfl) memory bank hc ht

theorem zero_accumulator (memory : Memory) (bank : Stack → List Bool) :
    computer.step (cfg .groupZero memory bank) =
      some (cfg (.emitMove 0) memory (Function.update bank random (false :: bank random))) := rfl

end Counting.Algorithm.KarpLubyRequest.Evaluation
