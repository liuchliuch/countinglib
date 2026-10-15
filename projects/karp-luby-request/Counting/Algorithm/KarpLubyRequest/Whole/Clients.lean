import Counting.Algorithm.KarpLubyRequest.Whole.Run
import Counting.Algorithm.KarpLubyRequest.Whole.Runtime
import Counting.Algorithm.KarpLubyRequest.Whole.ArrayObserver
import Counting.Algorithm.KarpLubyRequest.Whole.ArrayPrimitive
import Counting.Algorithm.KarpLubyRequest.Whole.FastRuntimeEnumeration

/-!
# Executing the complete raw-request source

Both observers interpret the unchanged finite statement syntax. The first finds
the halt using the array interpreter proved equal to TM2.step. The second starts
again from the original input and uses the independent primitive interpreter,
whose full cost and configuration are proved equal to Primitive.run. The array
address equivalence covers every physical stack; no transition is skipped.
-/
namespace Counting.Algorithm.KarpLubyRequest.Whole.Clients
open Turing Computability Holant.Complexity StackProtocol BinaryCompose GraphPreprocessing
open Counting.Algorithm.KarpLuby
set_option stderrAsMessages false
set_option maxRecDepth 1000000
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false

namespace Runtime
variable {K L S : Type} [DecidableEq K]
abbrev Program := L → TM2.Stmt (fun _ : K => Bool) L S

/-- Progress has no filesystem side effect unless the caller explicitly supplies
an attempt path. Each record is flushed independently of Lake's output buffering. -/
def report (message : String) : IO Unit := do
  let stamp ← IO.monoMsNow
  let line := toString stamp ++ " ms: " ++ message
  IO.eprintln line
  if let some path ← IO.getEnv "KARP_LUBY_RUNTIME_PROGRESS" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn line
      handle.flush

/-- Every iteration is the original transition by ArrayObserver.step_eq.
Only progress reporting uses IO; all machine operations are interpreted syntax. -/
def seek {n : ℕ} (describe : Option L → String) (e : Fin n ≃ K)
    (program : Program (K := K) (L := L) (S := S)) :
    ℕ → ℕ → ArrayObserver.Config n L S → IO (Option (ℕ × ArrayObserver.Config n L S))
  | 0, used, c => pure (if c.l.isNone then some (used, c) else none)
  | fuel + 1, used, c => do
      if c.l.isNone then return some (used, c)
      match ArrayObserver.step e program c with
      | none => return none
      | some next =>
        if (used + 1) % 8192 = 0 then
          report ("whole transition progress " ++ toString (used + 1) ++ ": " ++ describe next.l)
        seek describe e program fuel (used + 1) next

/-- Each finite chunk is the pure, equality-proved primitive interpreter.
The outer fuel is a host recursion bound; remaining is the measured source time. -/
def measureChunks {n : ℕ} (describe : Option L → String) (e : Fin n ≃ K)
    (program : Program (K := K) (L := L) (S := S)) :
    ℕ → ℕ → ℕ → ℕ → Option (ArrayObserver.Config n L S) →
      IO (ℕ × Option (ArrayObserver.Config n L S))
  | 0, remaining, _, cost, c =>
      if remaining = 0 then pure (cost, c)
      else throw (IO.userError "primitive observer exhausted its chunk bound")
  | chunks + 1, remaining, used, cost, c => do
      if remaining = 0 then return (cost, c)
      let amount := min 8192 remaining
      let measured := ArrayPrimitive.measure e program amount cost c
      report ("whole primitive progress " ++ toString (used + amount) ++ ": " ++
        describe (measured.2.bind fun cfg => cfg.l))
      measureChunks describe e program chunks (remaining - amount) (used + amount)
        measured.1 measured.2

/-- Both independent executions must have the exact original output bytes,
clean every physical stack, and restore every finite register. -/
def checkWord {n : ℕ} [BEq S] (describe : Option L → String) (e : Fin n ≃ K)
    (program : Program (K := K) (L := L) (S := S)) (main : L) (initial : S)
    (input output : K) (name : String) (raw expected : List Bool) (fuel : ℕ) : IO Unit := do
  let start := ArrayObserver.ofCfg e (⟨some main, initial, wordTape input raw⟩ :
    TM2.Cfg (fun _ : K => Bool) L S)
  let clean := fun (c : ArrayObserver.Config n L S) =>
    c.l.isNone && c.var == initial && (List.finRange n).all
      (fun i => ArrayObserver.read e c.stk (e i) == wordTape output expected (e i))
  report (name ++ ": executing original raw program on " ++ toString raw.length ++ " bits")
  match ← seek describe e program fuel 0 start with
  | none => throw (IO.userError (name ++ ": actual source did not halt within observer fuel"))
  | some (time, ending) =>
    unless clean ending do
      throw (IO.userError (name ++ ": original output bytes, full stack cleanup, or finite state differs"))
    report (name ++ ": " ++ toString time ++ " actual transitions; checking primitive interpreter")
    let measured ← measureChunks describe e program time time 0 0 (some start)
    match measured.2 with
    | none => throw (IO.userError (name ++ ": canonical primitive observer failed"))
    | some finish =>
      unless clean finish do
        throw (IO.userError (name ++ ": primitive endpoint differs from the original transition endpoint"))
    report (name ++ ": " ++ toString time ++ " actual transitions, " ++
      toString measured.1 ++ " primitive instructions, all " ++ toString n ++ " physical stacks clean")

end Runtime

/-- This legal zero-mass request uses unreduced rational fields 2/2 and 2/4. -/
def noncanonicalZero : List Bool :=
  Contract.join ⟨Encoding.frame [false, true, false] ++ Encoding.frame [],
    RationalFields.join ⟨false, [false], [false]⟩,
    RationalFields.join ⟨false, [false], [false, false]⟩, []⟩

def half : ℚ := ⟨1, 2, by decide, by decide⟩

def noncanonicalDecoded : ProgramEncoding.Request :=
  ⟨⟨3, []⟩, RationalFields.value ⟨false, [false], [false]⟩,
    RationalFields.value ⟨false, [false], [false, false]⟩, []⟩

/-- The noncanonical field words are accepted by the unchanged original decoder. -/
theorem noncanonical_zero_decodes :
    ProgramEncoding.request.decode noncanonicalZero = some noncanonicalDecoded := rfl


theorem noncanonical_parameters :
    noncanonicalDecoded.epsilon = 1 ∧ noncanonicalDecoded.delta = half := by
  constructor
  · change mkRat 2 2 = 1
    norm_num
  · change mkRat 2 4 = half
    apply Rat.ext
    · norm_num [Rat.num_mkRat, half]
    · norm_num [Rat.den_mkRat, half]

theorem noncanonical_zero_value :
    ProgramEncoding.evalBits noncanonicalZero = Encoding.encodeOutput 0 :=
  ZeroBranchSpec.evalBits_zero_mass _ _ noncanonical_zero_decodes (by decide)

def positiveRequest : ProgramEncoding.Request :=
  ⟨⟨0, [[]]⟩, 1, half, List.replicate 3456 false⟩

def positiveRaw : List Bool := ProgramEncoding.request.encode positiveRequest


theorem positive_samples :
    Program.requestedSamples (DNF.normalizeFormula positiveRequest.problem.formula)
      positiveRequest.epsilon = 576 := by decide


theorem positive_groups : Program.requestedGroups positiveRequest.delta = 6 := by decide


theorem positive_tape_length : positiveRequest.tape.length =
    Program.randomBitBudget (DNF.normalizeFormula positiveRequest.problem.formula) 576 6 := by decide


theorem empty_raw_actual : ∃ time, RunsExactly computer.step (initList computer [])
    (haltList computer (ProgramEncoding.evalBits [])) time := Whole.run []

theorem noncanonical_zero_actual : ∃ time,
    RunsExactly computer.step (initList computer noncanonicalZero)
      (haltList computer (ProgramEncoding.evalBits noncanonicalZero)) time := Whole.run noncanonicalZero

theorem positive_actual : ∃ time, RunsExactly computer.step (initList computer positiveRaw)
    (haltList computer (ProgramEncoding.evalBits positiveRaw)) time := Whole.run positiveRaw

/-- The runtime entry bank is exactly the original whole-machine entry bank. -/
def startConfiguration (raw : List Bool) : computer.Cfg :=
  ⟨some Whole.Runtime.main, Whole.Runtime.initial,
    @wordTape Whole.Runtime.Stack Whole.Runtime.stackDecidable Whole.Runtime.input raw⟩

theorem startConfiguration_eq (raw : List Bool) :
    startConfiguration raw = initList computer raw := by
  have hd : Whole.Runtime.stackDecidable = Whole.machine.decidableK := Subsingleton.elim _ _
  dsimp only [startConfiguration]
  rw [hd, Whole.Runtime.main_eq, Whole.Runtime.initial_eq, Whole.Runtime.input_eq]
  exact (Machine.init_eq machine raw).symm

theorem stack_coverage (k : Whole.Runtime.Stack) :
    ∃ i : Fin Whole.Runtime.FastEnumeration.count,
      Whole.Runtime.FastEnumeration.fastStackEquiv i = k :=
  Whole.Runtime.FastEnumeration.covers k


/-- The array observer begins with every stack and register of the original machine. -/
theorem array_start_eq (raw : List Bool) :
    ArrayObserver.toCfg Whole.Runtime.FastEnumeration.fastStackEquiv
      (ArrayObserver.ofCfg Whole.Runtime.FastEnumeration.fastStackEquiv (startConfiguration raw)) =
        initList computer raw :=
  (ArrayObserver.toCfg_ofCfg _ _).trans (startConfiguration_eq raw)

/-- Representation conversion commutes with the unchanged whole-machine step. -/
theorem array_transition_eq
    (c : ArrayObserver.Config Whole.Runtime.FastEnumeration.count
      Whole.Runtime.Label Whole.Runtime.State) :
    (ArrayObserver.step Whole.Runtime.FastEnumeration.fastStackEquiv Whole.Runtime.program c).map
        (ArrayObserver.toCfg Whole.Runtime.FastEnumeration.fastStackEquiv) =
      computer.step (ArrayObserver.toCfg Whole.Runtime.FastEnumeration.fastStackEquiv c) := by
  have h := @ArrayObserver.step_eq Whole.Runtime.Stack Whole.Runtime.Label Whole.Runtime.State
    Whole.Runtime.FastEnumeration.count Whole.Runtime.stackDecidable
    Whole.Runtime.FastEnumeration.fastStackEquiv Whole.Runtime.program c
  exact h.trans (congrFun Whole.Runtime.transition_eq _)

/-- Only broad finite-control phases are rendered; no bank or register is inspected. -/
def phase : Option Whole.Runtime.Label → String
  | none => "halt"
  | some (.inr (.inr _)) => "handoff"
  | some (.inr (.inl _)) => "evaluation"
  | some (.inl label) => match label with
    | .parameter _ => "preparation parser"
    | .formula _ => "preparation dense"
    | .mass _ | .massCheck => "preparation mass"
    | .counts _ => "preparation counts"
    | .budget _ | .gated => "preparation budget"
    | .clear _ | .done => "preparation cleanup"
    | .copyMove _ | .copyRestore _ => "preparation copy"
    | _ => "preparation framing"

/-- Compare the literal reference bytes before executing either interpreter.
The expected rational also independently fixes the intended tape scenario. -/
def checkRaw (name : String) (raw : List Bool) (value : ℚ) (fuel : ℕ) : IO Unit := do
  let expected := ProgramEncoding.evalBits raw
  unless expected == Encoding.encodeOutput value do
    throw (IO.userError (name ++ ": the original evaluator disagrees with the scenario value"))
  @Runtime.checkWord Whole.Runtime.Stack Whole.Runtime.Label Whole.Runtime.State
    Whole.Runtime.stackDecidable Whole.Runtime.FastEnumeration.count Whole.Runtime.stateBEq
    phase Whole.Runtime.FastEnumeration.fastStackEquiv Whole.Runtime.program Whole.Runtime.main
    Whole.Runtime.initial Whole.Runtime.input Whole.Runtime.output name raw expected fuel

/-- The positive case retains all original budget constants and all fair bits. -/
def checkSuite : IO Unit := do
  checkRaw "whole malformed empty word" [] 0 1000000
  checkRaw "whole legal noncanonical zero mass" noncanonicalZero 0 1000000
  checkRaw "whole nullary positive 576 samples x 6 groups, 3456 fair bits"
    positiveRaw 2 50000000

#eval checkSuite

end Counting.Algorithm.KarpLubyRequest.Whole.Clients
