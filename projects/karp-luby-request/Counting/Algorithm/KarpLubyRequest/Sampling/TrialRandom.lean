import Counting.Algorithm.KarpLubyRequest.Sampling.TrialBank

/-!
# Physical clock preparation and random-prefix consumption

The clock is copied from the retained mass word by two actual scans. The fair
reader consumes precisely that many random symbols and produces a canonical
binary rank. Two further scans copy the retained rows before the real selector
reset instruction. No assumption of canonical mass or row words is needed.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Trial
open Turing Computability Holant.Complexity StackProtocol

set_option backward.isDefEq.respectTransparency false

/-- The width supplied to the fair reader is physically copied, including both
scans and both end-of-word transitions. The retained mass word is unchanged. -/
theorem clock_copy (d : Data) (hc : d.clock = []) (hs : d.scratch = []) :
    RunsExactly computer.step (configuration .clockMove initial d)
      (configuration (.fair ()) initial {d with clock := d.mass})
      (2 * d.mass.length + 2) := by
  have hm : ExecutesAt computer.step .clockMove
      (copyMoveStmt .mass .scratch .clockMove .clockRestore) := by intro state tape; rfl
  have hr : ExecutesAt computer.step .clockRestore
      (copyRestoreStmt .mass .clock .scratch .clockRestore (.fair ())) := by
    intro state tape; rfl
  have h := Embedded.copy_into Stack.mass Stack.clock Stack.scratch (by decide) (by decide)
    (by decide) computer.step .clockMove .clockRestore (.fair ()) hm hr initial.2 d.tapes hc hs
  have hb : Function.update d.tapes Stack.clock (d.tapes .mass) =
      ({d with clock := d.mass} : Data).tapes := by
    funext k; cases k <;> rfl
  rw [hb] at h
  exact h

/-- The actual embedded reader preserves the random suffix and all unselected
stacks. Its success register remains set until the later selector reset. -/
theorem fair_call (rows massWord bits suffix : List Bool)
    (hlen : bits.length = massWord.length) :
    RunsExactly computer.step
      (configuration (.fair ()) initial
        {(inputData rows massWord (bits ++ suffix)) with clock := massWord})
      (configuration .rowsMove (none, none, none, true, false)
        {(inputData rows massWord suffix) with
          rank := encodeNat (BinaryArithmetic.value bits.reverse)})
      (bits.length + 1) := by
  apply MachineCall.run fairStacks Label.fair .rowsMove fairState
    FairTape.program program fair_code (none, false)
    (inputData rows massWord suffix).tapes
    (FairTape.cfg massWord (bits ++ suffix) [])
    (FairTape.finished true [] suffix (encodeNat (BinaryArithmetic.value bits.reverse)))
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro j h; cases j <;> first
        | rfl
        | exact (h 0 rfl).elim
        | exact (h 1 rfl).elim
        | exact (h 2 rfl).elim
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro j h; cases j <;> first
        | rfl
        | exact (h 0 rfl).elim
        | exact (h 1 rfl).elim
        | exact (h 2 rfl).elim
  · have hr := FairTape.read_exact bits massWord suffix [] hlen.symm
    dsimp only [FinTM2.step] at hr
    rw [FairTape.collect_encode] at hr
    exact hr

/-- Copy the actual stored row stream while retaining the reader's finite
registers. The selector receives this physical copy, not a semantic parameter. -/
theorem rows_copy (d : Data) (memory : Memory)
    (hr : d.remaining = []) (hs : d.scratch = []) :
    RunsExactly computer.step (configuration .rowsMove (none, memory) d)
      (configuration .selectStart (none, memory) {d with remaining := d.rows})
      (2 * d.rows.length + 2) := by
  have hm : ExecutesAt computer.step .rowsMove
      (copyMoveStmt .rows .scratch .rowsMove .rowsRestore) := by intro state tape; rfl
  have hc : ExecutesAt computer.step .rowsRestore
      (copyRestoreStmt .rows .remaining .scratch .rowsRestore .selectStart) := by
    intro state tape; rfl
  have h := Embedded.copy_into Stack.rows Stack.remaining Stack.scratch (by decide) (by decide)
    (by decide) computer.step .rowsMove .rowsRestore .selectStart hm hc memory d.tapes hr hs
  have hb : Function.update d.tapes Stack.remaining (d.tapes .rows) =
      ({d with remaining := d.rows} : Data).tapes := by
    funext k; cases k <;> rfl
  rw [hb] at h
  exact h

theorem select_start (d : Data) (state : State) :
    computer.step (configuration .selectStart state d) =
      some (configuration (.selector 0) initial d) := rfl

/-- Complete physical random prefix. Every mass-copy, fair-reader, row-copy and
reset transition is included. Arbitrary physical words, zero width and all-false
random bits are covered, and the unused random suffix is preserved exactly. -/
theorem random_prefix (rows massWord bits suffix : List Bool)
    (hlen : bits.length = massWord.length) :
    RunsExactly computer.step
      (configuration .clockMove initial (inputData rows massWord (bits ++ suffix)))
      (configuration (.selector 0) initial
        (selectionData rows massWord suffix (BinaryArithmetic.value bits.reverse)))
      (3 * massWord.length + 2 * rows.length + 6) := by
  have h1 := clock_copy (inputData rows massWord (bits ++ suffix)) rfl rfl
  have h2 := fair_call rows massWord bits suffix hlen
  have h3 := rows_copy
    ({(inputData rows massWord suffix) with
      rank := encodeNat (BinaryArithmetic.value bits.reverse)} : Data)
    (none, none, true, false) rfl rfl
  have h4 := runsExactly_one (select_start
    (selectionData rows massWord suffix (BinaryArithmetic.value bits.reverse))
    (none, none, none, true, false))
  convert ((h1.trans h2).trans h3).trans h4 using 1 <;>
    dsimp [inputData] <;> omega

end Counting.Algorithm.KarpLubyRequest.Sampling.Trial
