import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Bank

/-! # Returning frame operations in the actual group bank -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open FixedFieldMachines BinaryCompose
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

private theorem bank3_random (count old : List Bool) (f : Fin 6 → List Bool)
    (k : Fin 6) (a b work : List Bool) :
    tapes3 (bank count old f) random (.inr k) scratch a b work =
      bank count a (Function.update (Function.update f k b) 5 work) := by
  unfold tapes3
  change Function.update (Function.update (Function.update (bank count old f)
    random a) (.inr k) b) (.inr 5) work = _
  rw [update_random, update_field, update_field]

private theorem bank3_field (count old : List Bool) (f : Fin 6 → List Bool)
    (k : Fin 6) (a b work : List Bool) :
    tapes3 (bank count old f) (.inr k) random scratch a b work =
      bank count b (Function.update (Function.update f k a) 5 work) := by
  unfold tapes3
  change Function.update (Function.update (Function.update (bank count old f)
    (.inr k) a) random b) (.inr 5) work = _
  rw [update_field, update_random, update_field]

private theorem reset_field (f : Fin 6 → List Bool) (k : Fin 6) (hk : f k = []) :
    Function.update f k [] = f := by
  simpa only [hk] using Function.update_eq_self k f

private theorem reset_scratch (f : Fin 6 → List Bool) (k : Fin 6) (value : List Bool)
    (hk : k ≠ 5) (hf : f 5 = []) :
    Function.update (Function.update f k value) 5 [] = Function.update f k value := by
  apply reset_field
  rw [Function.update_of_ne (Ne.symm hk), hf]

/-- Two real scans remove one complete frame, retaining every other field. -/
theorem extract_field (scan restore next : Label) (k : Fin 6) (hk : k ≠ 5)
    (hs : ExecutesAt computer.step scan (Frame.scanStmt random scratch scan restore .bad))
    (hr : ExecutesAt computer.step restore (copyMoveStmt scratch (.inr k) restore next))
    (count word suffix : List Bool) (f : Fin 6 → List Bool) (hk0 : f k = []) (hwork : f 5 = []) :
    RunsExactly computer.step (config scan (bank count (Encoding.frame word ++ suffix) f))
      (config next (bank count suffix (Function.update f k word))) (2 * (word.length + 1)) := by
  have h := Frame.extract_exact random (.inr k) scratch
    (by intro h; cases h) (by intro h; cases h)
    (fun h => hk (Sum.inr.inj h)) computer.step scan restore next .bad hs hr
    SampleBody.machine.initial (bank count suffix f) word suffix []
  rw [← Contract.frame_eq] at h
  simp only [List.append_nil, bank3_random] at h
  rw [reset_scratch f k [] hk hwork, reset_field f k hk0,
    reset_scratch f k word hk hwork] at h
  exact h

/-- Two passes and the actual delimiter transition consume a field and prepend
its exact frame; scratch is returned empty. -/
theorem emit_field (move delimiter emit next : Label) (k : Fin 6) (hk : k ≠ 5)
    (hm : ExecutesAt computer.step move (copyMoveStmt (.inr k) scratch move delimiter))
    (hd : ExecutesAt computer.step delimiter (FrameEmit.delimiterStmt random emit))
    (he : ExecutesAt computer.step emit (FrameEmit.emitStmt scratch random emit next))
    (count suffix : List Bool) (f : Fin 6 → List Bool) (hwork : f 5 = []) :
    RunsExactly computer.step (config move (bank count suffix f))
      (config next (bank count (Encoding.frame (f k) ++ suffix) (Function.update f k [])))
      (2 * (f k).length + 3) := by
  have h := FrameEmit.prepend_exact (.inr k) random scratch
    (by intro h; cases h) (fun h => hk (Sum.inr.inj h)) (by intro h; cases h)
    computer.step move delimiter emit next hm hd he SampleBody.machine.initial
    (bank count suffix f) (f k) suffix
  rw [← Contract.frame_eq] at h
  simp only [bank3_field] at h
  rw [reset_scratch f k (f k) hk hwork, Function.update_eq_self,
    reset_scratch f k [] hk hwork] at h
  exact h

theorem header_extract (i : Fin 4) (count word suffix : List Bool) (f : Fin 6 → List Bool)
    (hfield : f ⟨i.val, by omega⟩ = []) (hwork : f 5 = []) :
    RunsExactly computer.step (config (.scan i) (bank count (Encoding.frame word ++ suffix) f))
      (config (headerNext i) (bank count suffix (Function.update f ⟨i.val, by omega⟩ word)))
      (2 * (word.length + 1)) := by
  apply extract_field (.scan i) (.restore i) (headerNext i) ⟨i.val, by omega⟩
    (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk, Fin.val_ofNat] at this; omega)
    (by intro state tape; rfl) (by intro state tape; rfl) count word suffix f hfield hwork

theorem inner_emit (i : Fin 2) (count suffix : List Bool) (f : Fin 6 → List Bool) (hwork : f 5 = []) :
    RunsExactly computer.step (config (.innerMove i) (bank count suffix f))
      (config (innerNext i) (bank count (Encoding.frame (f ⟨1-i.val, by omega⟩) ++ suffix)
        (Function.update f ⟨1-i.val, by omega⟩ [])))
      (2 * (f ⟨1-i.val, by omega⟩).length + 3) := by
  apply emit_field (.innerMove i) (.innerDelimiter i) (.innerEmit i) (innerNext i)
    ⟨1-i.val, by omega⟩ (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk, Fin.val_ofNat] at this; omega)
    ?_ (by intro state tape; rfl) (by intro state tape; rfl) count suffix f hwork
  intro state tape
  fin_cases i <;> rfl

theorem outer_emit (i : Fin 4) (count suffix : List Bool) (f : Fin 6 → List Bool) (hwork : f 5 = []) :
    RunsExactly computer.step (config (.outerMove i) (bank count suffix f))
      (config (outerNext i) (bank count (Encoding.frame (f ⟨3-i.val, by omega⟩) ++ suffix)
        (Function.update f ⟨3-i.val, by omega⟩ [])))
      (2 * (f ⟨3-i.val, by omega⟩).length + 3) := by
  apply emit_field (.outerMove i) (.outerDelimiter i) (.outerEmit i) (outerNext i)
    ⟨3-i.val, by omega⟩ (by intro h; have := congrArg Fin.val h; simp only [Fin.val_mk, Fin.val_ofNat] at this; omega)
    (by intro state tape; rfl) (by intro state tape; rfl) (by intro state tape; rfl)
    count suffix f hwork

end Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
