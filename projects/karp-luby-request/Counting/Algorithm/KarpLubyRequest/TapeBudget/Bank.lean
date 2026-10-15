import Counting.Algorithm.KarpLubyRequest.TapeBudget.Arithmetic
import Counting.Algorithm.KarpLubyRequest.MachineCall
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-!
# Preserving bank caller and zero-mass fast path

Four original words are retained: sample count, group count, total mass, and
random tape. The very first instruction peeks at the canonical mass. Zero mass
performs only one further EOF test and halts, returning `(valid, zeroMass)` in
finite control. The positive branch serializes actual copies of the retained
words, invokes the real arithmetic budget checker, and consumes its one-bit
answer. Every work stack is empty at the final endpoint.
-/
namespace Counting.Algorithm.KarpLubyRequest.TapeBudget.Bank
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose FixedFieldMachines GraphPreprocessing

abbrev Engine := Arithmetic.computes.machine
abbrev Stack := Fin 4 ⊕ (Fin 2 ⊕ Engine.K)
abbrev Label := Fin 20 ⊕ Engine.Label
/-- The first flag is validity; the second requests the direct zero output. -/
abbrev Status := Bool × Bool
abbrev Memory := Status × Engine.State
abbrev State := Option Bool × Memory
abbrev Config := Cfg Stack Label Memory

noncomputable instance stackFinite : Fintype Stack := inferInstanceAs (Fintype Stack)
noncomputable instance labelFinite : Fintype Label := inferInstanceAs (Fintype Label)
noncomputable instance stateFinite : Fintype State := inferInstanceAs (Fintype State)
instance stackDecidable : DecidableEq Stack := inferInstanceAs (DecidableEq Stack)

def original (i : Fin 4) : Stack := .inl i
def temporary : Stack := .inr (.inl 0)
def staging : Stack := .inr (.inl 1)
def destination : Stack := .inr (.inr Engine.input)
def own (l : Fin 20) : Label := .inl l
def engineMap : Engine.K ↪ Stack := ⟨fun k => .inr (.inr k), by intro a b h; exact Sum.inr.inj (Sum.inr.inj h)⟩
def engineLabel (l : Engine.Label) : Label := .inr l

def engineState : (Engine.State × (Option Bool × Status)) ≃ State :=
  (Equiv.prodComm _ _).trans (Equiv.prodAssoc _ _ _)

def index (j : Fin 3) : Fin 4 := ⟨2 - j.val, by omega⟩
def stageLabel (j : Fin 3) (phase : Fin 5) : Label := own ⟨4 + 5 * j.val + phase.val, by omega⟩
def next (j : Fin 3) : Label :=
  if h : j.val < 2 then stageLabel ⟨j.val + 1, by omega⟩ 0 else engineLabel Engine.main

def code (j : Fin 3) (phase : Fin 5) : Stmt Stack Label Memory :=
  if phase = 0 then copyMoveStmt (original (index j)) temporary (stageLabel j 0) (stageLabel j 1)
  else if phase = 1 then copyRestoreStmt (original (index j)) staging temporary (stageLabel j 1) (stageLabel j 2)
  else if phase = 2 then copyMoveStmt staging temporary (stageLabel j 2) (stageLabel j 3)
  else if phase = 3 then FrameEmit.delimiterStmt destination (stageLabel j 4)
  else FrameEmit.emitStmt temporary destination (stageLabel j 4) (next j)

def dispatch : Stmt Stack Label Memory :=
  .peek (original 2) (fun v bit => (bit, v.2))
    (.branch (fun v => v.1.isSome)
      (.load (fun v => (none, v.2)) (.goto (fun _ => own 2)))
      (.load (fun v => (none, v.2)) (.goto (fun _ => own 1))))

def zeroCase : Stmt Stack Label Memory :=
  .peek (original 3) (fun v bit => (bit, v.2))
    (.load (fun v => (none, (!v.1.isSome, true), v.2.2)) .halt)

def finish : Stmt Stack Label Memory :=
  .pop (engineMap Engine.output) (fun v bit => (bit, v.2))
    (.load (fun v => (none, (v.1.getD false, false), v.2.2)) .halt)

def localProgram (l : Fin 20) : Stmt Stack Label Memory :=
  if l = 0 then dispatch
  else if l = 1 then zeroCase
  else if l = 2 then copyMoveStmt (original 3) temporary (own 2) (own 3)
  else if l = 3 then copyRestoreStmt (original 3) destination temporary (own 3) (stageLabel 0 0)
  else if h : l.val < 19 then
    code ⟨(l.val - 4) / 5, by omega⟩ ⟨(l.val - 4) % 5, Nat.mod_lt _ (by decide)⟩
  else finish

noncomputable def program : Label → Stmt Stack Label Memory
  | .inl l => localProgram l
  | .inr l => MachineCall.block engineMap engineLabel (own 19) engineState (Engine.program l)

noncomputable abbrev computer : FinTM2 where
  K := Stack
  k₀ := original 3
  k₁ := engineMap Engine.output
  Γ _ := Bool
  Λ := Label
  main := own 0
  σ := State
  initialState := (none, (false, false), Engine.initial)
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

def tapes (old : Fin 4 → List Bool) (scratch staged : List Bool)
    (engine : Engine.K → List Bool) : Stack → List Bool :=
  Sum.elim old (Sum.elim (![scratch, staged]) engine)

def ready (old : Fin 4 → List Bool) (suffix : List Bool) : Stack → List Bool :=
  tapes old [] [] (wordTape Engine.input suffix)

def resultTapes (old : Fin 4 → List Bool) (output : List Bool) : Stack → List Bool :=
  tapes old [] [] (wordTape Engine.output output)

@[simp] theorem ready_original (old : Fin 4 → List Bool) (suffix : List Bool) (i : Fin 4) :
    ready old suffix (original i) = old i := rfl
@[simp] theorem ready_temporary (old : Fin 4 → List Bool) (suffix : List Bool) :
    ready old suffix temporary = [] := rfl
@[simp] theorem ready_staging (old : Fin 4 → List Bool) (suffix : List Bool) :
    ready old suffix staging = [] := rfl
@[simp] theorem ready_destination (old : Fin 4 → List Bool) (suffix : List Bool) :
    ready old suffix destination = suffix := wordTape_at Engine.input suffix

theorem code_eq (j : Fin 3) (phase : Fin 5) : program (stageLabel j phase) = code j phase := by
  fin_cases j <;> fin_cases phase <;> rfl

theorem initial_copy (old : Fin 4 → List Bool) (memory : Memory) :
    RunsExactly computer.step (cfg (own 2) memory (ready old []))
      (cfg (stageLabel 0 0) memory (ready old (old 3))) (2 * ((old 3).length + 1)) := by
  have hm : ExecutesAt computer.step (own 2) (copyMoveStmt (original 3) temporary (own 2) (own 3)) := by
    intro state stack; rfl
  have hr : ExecutesAt computer.step (own 3)
      (copyRestoreStmt (original 3) destination temporary (own 3) (stageLabel 0 0)) := by
    intro state stack; rfl
  have run := copy_exact (original 3) destination temporary (by intro h; cases h)
    (by intro h; cases h) (by intro h; cases h) computer.step (own 2) (own 3) (stageLabel 0 0)
    hm hr memory (ready old []) rfl
  simp only [ready_original, ready_destination, List.append_nil] at run
  have ht : Function.update (ready old []) destination (old 3) = ready old (old 3) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k =>
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k =>
        by_cases hk : k = Engine.input
        · subst k; rfl
        · simp only [ready, tapes, destination, wordTape, Function.update_apply,
            Sum.elim_inr, hk, reduceCtorEq, ite_false, Sum.inr.injEq]
  rw [ht] at run
  exact run

/-- Generic retained-copy plus canonical frame emission in this real caller. -/
theorem prepend_field (old : Fin 4 → List Bool) (suffix : List Bool)
    (memory : Memory) (j : Fin 3) :
    RunsExactly computer.step (cfg (stageLabel j 0) memory (ready old suffix))
      (cfg (next j) memory
        (ready old (Holant.Algebraic.frame (old (index j)) ++ suffix)))
      (4 * (old (index j)).length + 5) := by
  let word := old (index j)
  let copied := Function.update (ready old suffix) staging word
  have hmove : ExecutesAt computer.step (stageLabel j 0)
      (copyMoveStmt (original (index j)) temporary (stageLabel j 0) (stageLabel j 1)) := by
    intro state stack
    change some (TM2.stepAux (program (stageLabel j 0)) state stack) = _
    rw [code_eq]; rfl
  have hrestore : ExecutesAt computer.step (stageLabel j 1)
      (copyRestoreStmt (original (index j)) staging temporary (stageLabel j 1) (stageLabel j 2)) := by
    intro state stack
    change some (TM2.stepAux (program (stageLabel j 1)) state stack) = _
    rw [code_eq]; rfl
  have cp := copy_exact (original (index j)) staging temporary
    (by intro h; cases h) (by intro h; cases h) (by decide) computer.step
    (stageLabel j 0) (stageLabel j 1) (stageLabel j 2) hmove hrestore memory (ready old suffix) rfl
  simp only [ready_original, ready_staging, List.append_nil] at cp
  have hm : ExecutesAt computer.step (stageLabel j 2)
      (copyMoveStmt staging temporary (stageLabel j 2) (stageLabel j 3)) := by
    intro state stack
    change some (TM2.stepAux (program (stageLabel j 2)) state stack) = _
    rw [code_eq]; rfl
  have hd : ExecutesAt computer.step (stageLabel j 3)
      (FrameEmit.delimiterStmt destination (stageLabel j 4)) := by
    intro state stack
    change some (TM2.stepAux (program (stageLabel j 3)) state stack) = _
    rw [code_eq]; rfl
  have he : ExecutesAt computer.step (stageLabel j 4)
      (FrameEmit.emitStmt temporary destination (stageLabel j 4) (next j)) := by
    intro state stack
    change some (TM2.stepAux (program (stageLabel j 4)) state stack) = _
    rw [code_eq]; rfl
  have emit := FrameEmit.prepend_exact staging destination temporary
    (by intro h; cases h) (by decide) (by intro h; cases h) computer.step
    (stageLabel j 2) (stageLabel j 3) (stageLabel j 4) (next j)
    hm hd he memory (ready old suffix) word suffix
  have before : tapes3 (ready old suffix) staging destination temporary word suffix [] = copied := by
    funext k
    cases k with
    | inl k => rfl
    | inr k =>
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k =>
        by_cases hk : k = Engine.input
        · subst k; rfl
        · simp only [tapes3, ready, tapes, copied, staging, temporary, destination,
            wordTape, Function.update_apply, Sum.elim_inr, hk, reduceCtorEq, ite_false, Sum.inr.injEq]
  have after : tapes3 (ready old suffix) staging destination temporary []
      (Holant.Algebraic.frame word ++ suffix) [] = ready old (Holant.Algebraic.frame word ++ suffix) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k =>
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k =>
        by_cases hk : k = Engine.input
        · subst k; rfl
        · simp only [tapes3, ready, tapes, staging, temporary, destination,
            wordTape, Function.update_apply, Sum.elim_inr, hk, reduceCtorEq, ite_false, Sum.inr.injEq]
  rw [before, after] at emit
  convert cp.trans emit using 1 <;> dsimp only [word] <;> omega

/-- Literal word materialized by three real frame emissions. -/
def serialized (old : Fin 4 → List Bool) : List Bool :=
  Holant.Algebraic.frame (old 0) ++
  (Holant.Algebraic.frame (old 1) ++
  (Holant.Algebraic.frame (old 2) ++ old 3))

def serializeTime (old : Fin 4 → List Bool) : ℕ :=
  2 * (old 3).length + 4 * ((old 0).length + (old 1).length + (old 2).length) + 17

/-- This run starts only after the mass test; it retains the complete input
bank while physically preparing the nonzero branch's arithmetic input. -/
theorem serialize (old : Fin 4 → List Bool) (memory : Memory) :
    RunsExactly computer.step (cfg (own 2) memory (ready old []))
      (cfg (engineLabel Engine.main) memory (ready old (serialized old)))
      (serializeTime old) := by
  have first := initial_copy old memory
  have h0 := prepend_field old (old 3) memory 0
  have h1 := prepend_field old (Holant.Algebraic.frame (old 2) ++ old 3) memory 1
  have h2 := prepend_field old
    (Holant.Algebraic.frame (old 1) ++ (Holant.Algebraic.frame (old 2) ++ old 3)) memory 2
  change RunsExactly computer.step _ (cfg (stageLabel 1 0) memory _) _ at h0
  change RunsExactly computer.step _ (cfg (stageLabel 2 0) memory _) _ at h1
  change RunsExactly computer.step _ (cfg (engineLabel Engine.main) memory _) _ at h2
  have hi0 : index 0 = 2 := rfl
  have hi1 : index 1 = 1 := rfl
  have hi2 : index 2 = 0 := rfl
  rw [hi0] at h0
  rw [hi1] at h1
  rw [hi2] at h2
  convert ((first.trans h0).trans h1).trans h2 using 1
  · rfl
  · unfold serializeTime; omega

set_option maxHeartbeats 1000000 in
/-- Invoke exactly the arithmetic source program, preserving every original
word and the finite caller status. Its Boolean output is the only new word. -/
theorem arithmetic_run (old : Fin 4 → List Bool) (status : Status) (x : Arithmetic.Input) :
    RunsExactly computer.step
      (cfg (engineLabel Engine.main) (status, Engine.initial)
        (ready old (Arithmetic.inputEncoding.encode x)))
      (cfg (own 19) (status, Engine.initial)
        (resultTapes old (encodingBoolBool.encode (Arithmetic.valid x))))
      (Arithmetic.computes.outputs x).steps := by
  let input := Arithmetic.inputEncoding.encode x
  let output := encodingBoolBool.encode (Arithmetic.valid x)
  have code : ∀ l, program (engineLabel l) =
      MachineCall.block engineMap engineLabel (own 19) engineState (Engine.program l) := by
    intro l; rfl
  have ha : Embedded.Rel engineMap engineLabel (own 19) (ready old [])
      (StateAdapter.cfg engineState (none, status) (initList Engine.computer input))
      (cfg (engineLabel Engine.main) (status, Engine.initial) (ready old input)) := by
    rw [Machine.init_eq]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro k hk
      cases k with
      | inl k => rfl
      | inr k =>
        cases k with
        | inl k => rfl
        | inr k => exact False.elim (hk k rfl)
  have hz : Embedded.Rel engineMap engineLabel (own 19) (ready old [])
      (StateAdapter.cfg engineState (none, status) (haltList Engine.computer output))
      (cfg (own 19) (status, Engine.initial) (resultTapes old output)) := by
    rw [Machine.halt_eq]
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro k hk
      cases k with
      | inl k => rfl
      | inr k =>
        cases k with
        | inl k => rfl
        | inr k => exact False.elim (hk k rfl)
  have hr : (fun p => p.bind (TM2.step Engine.program))^[(Arithmetic.computes.outputs x).steps]
      (some (initList Engine.computer input)) = some (haltList Engine.computer output) :=
    (Arithmetic.computes.outputs x).evals_in_steps
  exact MachineCall.run engineMap engineLabel (own 19) engineState Engine.program
    program code (none, status) (ready old []) _ _ _ _ _ ha hz hr

end
end Counting.Algorithm.KarpLubyRequest.TapeBudget.Bank
