import Counting.Algorithm.KarpLubyRequest.Dense.NormalizeRaw

/-! # Halted finite call interface for a normalized raw term -/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Normalize
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

/-- The status flag is physically set by the terminal instruction. An empty row
can still be successful, as required for an empty term over zero variables. -/
def returned {τ : Type} (memory : τ) (original : List Bool) (result : Option CellCodec.Cells) :
    Cfg (Fin 8) Label (Bool × τ) where
  l := none
  var := (none, (result.isSome, memory))
  stk := tapes original [] (result.elim [] CellCodec.encode) [] [] [] [] []

theorem finish_step {τ : Type} (bit : Bool) (memory : τ) (original : List Bool)
    (result : Option CellCodec.Cells) :
    TM2.step (program (τ := τ)) (finished bit memory original result) =
      some (returned memory original result) := by
  cases result <;> rfl

/-- This is an actual halting run, ready for the canonical F1 halt-redirection
compiler. The result flag and all saved caller memory are explicit. -/
theorem normalize_call {τ : Type} (old : Bool) (memory : τ)
    (original raw : List Bool) (term : DNF.RawTerm original.length)
    (h : (Encoding.list (Encoding.literal original.length)).decode raw = some term) :
    ∃ time : ℕ, time ≤ rawCost original.length raw.length + 1 ∧
      RunsExactly (TM2.step (program (τ := τ)))
        (cfg .headerScan (old, memory) (tapes original raw [] [] [] [] [] []))
        (returned memory original (DenseNormalization.normalize original.length term).value) time := by
  obtain ⟨bit, time, bound, run⟩ := normalize_raw old memory original raw term h
  refine ⟨1 + time, by omega, ?_⟩
  exact run.trans (runsExactly_one (finish_step bit memory original _))

end Counting.Algorithm.KarpLubyRequest.Dense.Normalize
