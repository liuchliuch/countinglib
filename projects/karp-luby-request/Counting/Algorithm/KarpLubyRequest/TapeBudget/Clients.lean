import Counting.Algorithm.KarpLubyRequest.TapeBudget.Run

/-! Boundary contracts of the real bank program. The literal Boolean tests
below inspect only the specification. The execution theorems refer to the
actual finite caller, and the zero-path primitive counter is reduced directly.
No test pretends to execute exponentially many sample iterations. -/
namespace Counting.Algorithm.KarpLubyRequest.TapeBudget.Clients
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing
open Bank
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

example : Arithmetic.valid (3, 2, 8, List.replicate 24 false) = true := by decide
example : Arithmetic.valid (3, 2, 8, List.replicate 23 false) = false := by decide
example : Arithmetic.valid (3, 2, 8, List.replicate 25 true) = false := by decide
example : Arithmetic.valid (0, 2^128, 1, []) = true := by decide
example : Arithmetic.valid (2^128, 0, 1, []) = true := by decide
example : Arithmetic.valid (2^128, 2^128, 1, [true]) = false := by decide
example : Arithmetic.valid (2^128, 2^128, 0, []) = true := by decide
example : Arithmetic.valid (2^128, 2^128, 0, [false]) = false := by decide

/-- Enormous binary parameters still take exactly two actual transitions on
zero mass. The original tape is retained even when rejected. -/
example (tape : List Bool) (status : Status) :
    RunsExactly computer.step
      (cfg (own 0) (status, Engine.initial) (ready (prepared (2^128, 2^128, 0, tape)) []))
      (finished (prepared (2^128, 2^128, 0, tape)) (decide (tape = [])) true) 2 :=
  zero_run _ _ rfl

/-- Direct interpretation of the zero path costs exactly seven primitive
instructions: peek/branch/load/goto, then peek/load/halt. -/
theorem zero_primitive (old : Fin 4 → List Bool) (status : Status) (hm : old 2 = []) :
    (Primitive.run program 2
      (some (cfg (own 0) (status, Engine.initial) (ready old [])))).1 = 7 := by
  simp [Primitive.run, Primitive.tick, program, localProgram, own, dispatch, zeroCase,
    cfg, TM2Cost.primitiveRun, ready_original, hm]

example (status : Status) :
    (Primitive.run program 2
      (some (cfg (own 0) (status, Engine.initial)
        (ready (prepared (2^128, 2^128, 0, [false])) [])))).1 = 7 :=
  zero_primitive _ _ rfl

/-- The positive case invokes the actual compiled arithmetic checker. Its
source execution certificate supplies the exact transition count. -/
example (status : Status) :
    RunsExactly computer.step
      (cfg (own 0) (status, Engine.initial) (ready (prepared (3, 2, 8, List.replicate 24 false)) []))
      (finished (prepared (3, 2, 8, List.replicate 24 false)) true false)
      (1 + ((Arithmetic.computes.outputs (3, 2, 8, List.replicate 24 false)).steps +
        (serializeTime (prepared (3, 2, 8, List.replicate 24 false)) + 1))) :=
  positive_run _ _ (by decide)

example (tape : List Bool) :
    (finished (prepared (2^128, 2^128, 0, tape)) (decide (tape = [])) true).stk (original 3) = tape := rfl

example (tape : List Bool) (k : Fin 2 ⊕ Engine.K) :
    (finished (prepared (2^128, 2^128, 0, tape)) (decide (tape = [])) true).stk (.inr k) = [] :=
  finished_work _ _ _ k

end Counting.Algorithm.KarpLubyRequest.TapeBudget.Clients
