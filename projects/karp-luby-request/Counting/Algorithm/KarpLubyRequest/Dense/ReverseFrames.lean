import Counting.Algorithm.KarpLubyRequest.Dense.CellCodec
import Counting.Algorithm.KarpLubyRequest.ListFields
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-!
# Actual reversal of a list of framed words

The existing H1 frame scanner and emitter are composed directly. Each input
frame is decoded onto the scratch stack in reverse, then emitted in its original
bit order onto the front of the output list. This provides the tail-first literal
order of the canonical dense normalizer without changing literal semantics.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.ReverseFrames
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Turing.TM2.Stmt
open Counting.Algorithm.KarpLuby
open FixedFieldMachines

variable {K Λ τ : Type} [DecidableEq K]
abbrev Stacks (K : Type) := Fin 3 ↪ K

structure Labels (Λ : Type) where
  check : Λ
  scan : Λ
  delimiter : Λ
  emit : Λ
  next : Λ
  bad : Λ

abbrev tapes (st : Stacks K) (frame : K → List Bool)
    (input output scratch : List Bool) : K → List Bool :=
  tapes3 frame (st 0) (st 1) (st 2) input output scratch

def checkStmt (input : K) (scan next : Λ) : Stmt K Λ τ :=
  peek input (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (load (fun v => (none, v.2)) (goto (fun _ => scan)))
      (load (fun v => (none, v.2)) (goto (fun _ => next))))

structure Executes (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (st : Stacks K) (lab : Labels Λ) : Prop where
  check : ExecutesAt step lab.check (checkStmt (st 0) lab.scan lab.next)
  scan : ExecutesAt step lab.scan
    (Frame.scanStmt (st 0) (st 2) lab.scan lab.delimiter lab.bad)
  delimiter : ExecutesAt step lab.delimiter (FrameEmit.delimiterStmt (st 1) lab.emit)
  emit : ExecutesAt step lab.emit (FrameEmit.emitStmt (st 2) (st 1) lab.emit lab.check)

variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (st : Stacks K) (lab : Labels Λ)
variable (exec : Executes step st lab) (memory : τ) (frame : K → List Bool)
include exec

theorem check_nil (output : List Bool) :
    step (cfg lab.check memory (tapes st frame [] output [])) =
      some (cfg lab.next memory (tapes st frame [] output [])) := by
  rw [cfg, exec.check]
  simp [checkStmt, TM2.stepAux, cfg, tapes, tapes3, st.injective.eq_iff]

theorem check_frame (word rest output : List Bool) :
    step (cfg lab.check memory (tapes st frame (Encoding.frame word ++ rest) output [])) =
      some (cfg lab.scan memory (tapes st frame (Encoding.frame word ++ rest) output [])) := by
  cases word <;> rw [cfg, exec.check] <;>
    simp [checkStmt, TM2.stepAux, cfg, tapes, tapes3, st.injective.eq_iff, Encoding.frame]

/-- One physical frame is transferred, with its internal bit order unchanged. -/
theorem transfer_exact (word rest output : List Bool) :
    RunsExactly step
      (cfg lab.check memory (tapes st frame (Encoding.frame word ++ rest) output []))
      (cfg lab.check memory (tapes st frame rest (Encoding.frame word ++ output) []))
      (2 * word.length + 4) := by
  have first := runsExactly_one (check_frame step st lab exec memory frame word rest output)
  have scan := Frame.scan_exact (st 0) (st 1) (st 2)
    (fun h => by have := st.injective h; contradiction)
    (fun h => by have := st.injective h; contradiction)
    step lab.scan lab.delimiter lab.bad exec.scan memory frame word rest output []
  have delimiter : RunsExactly step
      (cfg lab.delimiter memory (tapes st frame rest output word.reverse))
      (cfg lab.emit memory (tapes st frame rest (false :: output) word.reverse)) 1 := by
    apply runsExactly_one
    rw [cfg, exec.delimiter]
    simp [FrameEmit.delimiterStmt, TM2.stepAux, cfg, tapes, tapes3, st.injective.eq_iff]
    funext k
    by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;> by_cases h2 : k = st 2 <;>
      simp_all [Function.update_apply, st.injective.eq_iff]
  have emit := FrameEmit.emit_exact (st 0) (st 1) (st 2)
    (fun h => by have := st.injective h; contradiction)
    step lab.emit lab.check exec.emit memory frame rest (false :: output) word.reverse
  have body : FrameEmit.body word ++ false :: output = Encoding.frame word ++ output := by
    rw [Contract.frame_eq, ← FrameEmit.body_delimiter]
    simp only [List.append_assoc, List.singleton_append]
  simp only [← Contract.frame_eq, List.append_nil] at scan
  simp only [List.reverse_reverse, List.length_reverse, body] at emit
  convert ((first.trans scan).trans delimiter).trans emit using 1 <;> omega

/-- No decoded list length appears in the runtime: the input is traversed until
its physical end, with one terminator test after the last frame. -/
theorem reverse_exact (words : List (List Bool)) (output : List Bool) :
    RunsExactly step
      (cfg lab.check memory (tapes st frame (Encoding.frames words) output []))
      (cfg lab.next memory (tapes st frame [] (Encoding.frames words.reverse ++ output) []))
      (2 * (words.map List.length).sum + 4 * words.length + 1) := by
  induction words generalizing output with
  | nil => simpa [Encoding.frames] using runsExactly_one (check_nil step st lab exec memory frame output)
  | cons word words ih =>
    have first := transfer_exact step st lab exec memory frame word (Encoding.frames words) output
    have rest := ih (Encoding.frame word ++ output)
    have whole := first.trans rest
    have append : ∀ xs ys : List (List Bool),
        Encoding.frames (xs ++ ys) = Encoding.frames xs ++ Encoding.frames ys := by
      intro xs ys
      induction xs with
      | nil => rfl
      | cons x xs hx => simp [Encoding.frames, hx, List.append_assoc]
    simpa [Encoding.frames, List.reverse_cons, append, List.append_assoc,
      Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using whole

end Counting.Algorithm.KarpLubyRequest.Dense.ReverseFrames
