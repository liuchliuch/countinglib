import Counting.Algorithm.KarpLubyRequest.Dense.WriteProgram

/-! # Exact transitions and returning subroutines of the dense-row writer -/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Write
open Turing Computability Holant.Complexity StackProtocol IntegerArithmetic

variable {K Λ τ : Type} [DecidableEq K]
variable (step : Cfg K Λ (Bool × τ) → Option (Cfg K Λ (Bool × τ)))
variable (st : Stacks K) (lab : Labels Λ) (exec : Executes step st lab)
variable (b : Bool) (memory : τ) (frame : K → List Bool)

include exec

theorem empty_step (counter pref : List Bool) :
    step (cfg lab.loop (b, memory) (tapes st frame [] counter pref [])) =
      some (cfg lab.clearCounter (b, memory) (tapes st frame [] counter pref [])) := by
  rw [cfg, exec.loop]
  simp [checkStmt, TM2.stepAux, cfg]

theorem zero_step (tag value : Bool) (row pref : List Bool) :
    step (cfg lab.loop (b, memory) (tapes st frame (tag :: value :: row) [] pref [])) =
      some (cfg lab.write (b, memory) (tapes st frame (tag :: value :: row) [] pref [])) := by
  rw [cfg, exec.loop]
  simp [checkStmt, TM2.stepAux, cfg]

theorem positive_step (tag value : Bool) (row counter pref : List Bool) (hc : counter ≠ []) :
    step (cfg lab.loop (b, memory) (tapes st frame (tag :: value :: row) counter pref [])) =
      some (cfg lab.skip (b, memory) (tapes st frame (tag :: value :: row) counter pref [])) := by
  cases counter with
  | nil => contradiction
  | cons c counter =>
    rw [cfg, exec.loop]
    simp [checkStmt, TM2.stepAux, cfg]

theorem skip_step (tag value : Bool) (row counter pref : List Bool) :
    step (cfg lab.skip (b, memory) (tapes st frame (tag :: value :: row) counter pref [])) =
      some (cfg lab.borrow (b, memory) (tapes st frame row counter (value :: tag :: pref) [])) := by
  rw [cfg, exec.skip]
  simp [skipStmt, TM2.stepAux, cfg]

theorem write_none_step (row pref : List Bool) :
    step (cfg lab.write (b, memory) (tapes st frame (false :: false :: row) [] pref [])) =
      some (cfg lab.restoreRow (b, memory) (tapes st frame (true :: b :: row) [] pref [])) := by
  rw [cfg, exec.write]
  simp [writeStmt, TM2.stepAux, cfg]

theorem write_same_step (row pref : List Bool) :
    step (cfg lab.write (b, memory) (tapes st frame (true :: b :: row) [] pref [])) =
      some (cfg lab.restoreRow (b, memory) (tapes st frame (true :: b :: row) [] pref [])) := by
  rw [cfg, exec.write]
  simp [writeStmt, TM2.stepAux, cfg]

theorem write_conflict_step (old : Bool) (h : old ≠ b) (row pref : List Bool) :
    step (cfg lab.write (b, memory) (tapes st frame (true :: old :: row) [] pref [])) =
      some (cfg lab.clearCounter (b, memory) (tapes st frame row [] pref [])) := by
  rw [cfg, exec.write]
  simp [writeStmt, TM2.stepAux, cfg, h]

omit exec in
private theorem as_counter (row counter pref scratch : List Bool) :
    tapes st frame row counter pref scratch =
      tapes3 (Function.update frame (st 2) pref) (st 1) (st 0) (st 3)
        counter row scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, Allocate.tapes, tapes3, Function.update_apply, st.injective.eq_iff]

theorem decrement_exact (row counter pref : List Bool) :
    RunsExactly step (cfg lab.borrow (b, memory) (tapes st frame row counter pref []))
      (cfg lab.loop (b, memory) (tapes st frame row (decrement counter) pref []))
      (2 * (borrowCount counter + 1)) := by
  simpa only [as_counter] using
    CountedList.Counter.decrement_exact (st 1) (st 0) (st 3)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.borrow lab.restoreCounter lab.loop exec.borrow (b, memory)
      (Function.update frame (st 2) pref) exec.restoreCounter counter row

omit exec in
private theorem as_restore (row counter pref scratch : List Bool) :
    tapes st frame row counter pref scratch =
      tapes3 (Function.update frame (st 3) scratch) (st 2) (st 1) (st 0)
        pref counter row := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, Allocate.tapes, tapes3, Function.update_apply, st.injective.eq_iff]

theorem restore_exact (row pref : List Bool) :
    RunsExactly step (cfg lab.restoreRow (b, memory) (tapes st frame row [] pref []))
      (cfg lab.good (b, memory) (tapes st frame (pref.reverse ++ row) [] [] []))
      (pref.length + 1) := by
  simpa only [as_restore] using
    copy_move_exact (st 2) (st 1) (st 0)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.restoreRow lab.good exec.restoreRow (b, memory)
      (Function.update frame (st 3) []) pref [] row

/-- A rejecting execution erases all partially processed data; no index value
appears in its transition count, only the lengths of the stored words. -/
theorem cleanup_exact (row counter pref : List Bool) :
    RunsExactly step (cfg lab.clearCounter (b, memory) (tapes st frame row counter pref []))
      (cfg lab.bad (b, memory) (tapes st frame [] [] [] []))
      (row.length + counter.length + pref.length + 3) := by
  have hc := clear_exact step (st 1) lab.clearCounter lab.clearPrefix exec.clearCounter
    (b, memory) (tapes st frame row counter pref [])
  have hp := clear_exact step (st 2) lab.clearPrefix lab.clearRow exec.clearPrefix
    (b, memory) (tapes st frame row [] pref [])
  have hr := clear_exact step (st 0) lab.clearRow lab.bad exec.clearRow
    (b, memory) (tapes st frame row [] [] [])
  simp [tapes_at, update_counter, update_prefix, update_row] at hc hp hr
  convert (hc.trans hp).trans hr using 1 <;> omega

end Counting.Algorithm.KarpLubyRequest.Dense.Write
