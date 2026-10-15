import Counting.Algorithm.KarpLubyRequest.ParameterValidation
import Counting.Algorithm.KarpLubyRequest.ParameterCounts
import Counting.Algorithm.KarpLubyRequest.MachineCall
import Holant.Complexity.FixedFieldMachines.FrameEmit

/-!
# Physical parameter-bank serialization and returning count execution

The original parser/parameter bank is preserved. A separate canonical clause
count and three Boolean work stacks feed the actual arithmetic machine. Every
prefix frame is produced by H1's physical `FrameEmit` program after a retained
copy of the original word. This is a prepared-bank calling convention, not a
claim that five semantic fields are free inputs to a raw-request machine.
-/
namespace Counting.Algorithm.KarpLubyRequest.ParameterCountsBank
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose FixedFieldMachines GraphPreprocessing
open Counting.Algorithm.KarpLuby

abbrev Arithmetic := ParameterCounts.computes.machine
abbrev Stack := ParameterProgram.Stack ⊕ (Fin 3 ⊕ Arithmetic.K)
abbrev Label := Fin 23 ⊕ Arithmetic.Label
abbrev Memory := ParameterProgram.Memory × Arithmetic.State
abbrev State := Option Bool × Memory
abbrev Config := Cfg Stack Label Memory

noncomputable instance stackFinite : Fintype Stack := inferInstanceAs (Fintype Stack)
noncomputable instance labelFinite : Fintype Label := inferInstanceAs (Fintype Label)
noncomputable instance stateFinite : Fintype State := by
  letI : Fintype (Option Bool × ParameterProgram.Memory) := ParameterProgram.stateFinite
  exact Fintype.ofEquiv ((Option Bool × ParameterProgram.Memory) × Arithmetic.State)
    (Equiv.prodAssoc _ _ _)

instance stackDecidable : DecidableEq Stack := inferInstanceAs (DecidableEq Stack)

def original (i : Fin 4) : Stack := .inl (ParameterProgram.canonical i)
def clauses : Stack := .inr (.inl 0)
def temporary : Stack := .inr (.inl 1)
def staging : Stack := .inr (.inl 2)
def destination : Stack := .inr (.inr Arithmetic.input)
def own (l : Fin 23) : Label := .inl l
def arithmeticMap : Arithmetic.K ↪ Stack := ⟨fun k => .inr (.inr k), by intro a b h; exact Sum.inr.inj (Sum.inr.inj h)⟩
def arithmeticLabel (l : Arithmetic.Label) : Label := .inr l

def arithmeticState : (Arithmetic.State × (Option Bool × ParameterProgram.Memory)) ≃ State :=
  (Equiv.prodComm _ _).trans (Equiv.prodAssoc _ _ _)

def index (j : Fin 4) : Fin 4 := ⟨3 - j.val, by omega⟩
def stageLabel (j : Fin 4) (phase : Fin 5) : Label := own ⟨2 + 5 * j.val + phase.val, by omega⟩
def next (j : Fin 4) : Label :=
  if h : j.val < 3 then stageLabel ⟨j.val + 1, by omega⟩ 0 else arithmeticLabel Arithmetic.main

def code (j : Fin 4) (phase : Fin 5) : Stmt Stack Label Memory :=
  if phase = 0 then copyMoveStmt (original (index j)) temporary (stageLabel j 0) (stageLabel j 1)
  else if phase = 1 then copyRestoreStmt (original (index j)) staging temporary (stageLabel j 1) (stageLabel j 2)
  else if phase = 2 then copyMoveStmt staging temporary (stageLabel j 2) (stageLabel j 3)
  else if phase = 3 then FrameEmit.delimiterStmt destination (stageLabel j 4)
  else FrameEmit.emitStmt temporary destination (stageLabel j 4) (next j)

/-- Only bounded label arithmetic is used in finite control. -/
def localProgram (l : Fin 23) : Stmt Stack Label Memory :=
  if l = 0 then copyMoveStmt clauses temporary (own 0) (own 1)
  else if l = 1 then copyRestoreStmt clauses destination temporary (own 1) (stageLabel 0 0)
  else if h : l.val < 22 then
    code ⟨(l.val - 2) / 5, by omega⟩ ⟨(l.val - 2) % 5, Nat.mod_lt _ (by decide)⟩
  else .halt

noncomputable def program : Label → Stmt Stack Label Memory
  | .inl l => localProgram l
  | .inr l => Embedded.block arithmeticMap arithmeticLabel (own 22)
      (StateAdapter.block arithmeticState (Arithmetic.program l))

noncomputable abbrev computer : FinTM2 where
  K := Stack
  k₀ := clauses
  k₁ := arithmeticMap Arithmetic.output
  Γ _ := Bool
  Λ := Label
  main := own 0
  σ := State
  initialState := (none, (true, BinaryArithmetic.Comparison.initial), Arithmetic.initial)
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

/-- The old bank is retained literally. Only these selected work stacks are
used; the arithmetic machine's remaining stacks are clean. -/
def tapes (old : ParameterProgram.Stack → List Bool) (m scratch staged : List Bool)
    (arithmetic : Arithmetic.K → List Bool) : Stack → List Bool :=
  Sum.elim old (Sum.elim (![m, scratch, staged]) arithmetic)

def ready (old : ParameterProgram.Stack → List Bool) (m suffix : List Bool) : Stack → List Bool :=
  tapes old m [] [] (wordTape Arithmetic.input suffix)

@[simp] theorem ready_original (old : ParameterProgram.Stack → List Bool)
    (m suffix : List Bool) (i : Fin 4) :
    ready old m suffix (original i) = old (ParameterProgram.canonical i) := rfl
@[simp] theorem ready_clauses (old : ParameterProgram.Stack → List Bool)
    (m suffix : List Bool) : ready old m suffix clauses = m := rfl
@[simp] theorem ready_temporary (old : ParameterProgram.Stack → List Bool)
    (m suffix : List Bool) : ready old m suffix temporary = [] := rfl
@[simp] theorem ready_staging (old : ParameterProgram.Stack → List Bool)
    (m suffix : List Bool) : ready old m suffix staging = [] := rfl
@[simp] theorem ready_destination (old : ParameterProgram.Stack → List Bool)
    (m suffix : List Bool) : ready old m suffix destination = suffix := by
  exact wordTape_at Arithmetic.input suffix

theorem code_eq (j : Fin 4) (phase : Fin 5) : program (stageLabel j phase) = code j phase := by
  fin_cases j <;> fin_cases phase <;> rfl

theorem initial_copy (old : ParameterProgram.Stack → List Bool) (m : List Bool) (memory : Memory) :
    RunsExactly computer.step (cfg (own 0) memory (ready old m []))
      (cfg (stageLabel 0 0) memory (ready old m m)) (2 * (m.length + 1)) := by
  have hm : ExecutesAt computer.step (own 0) (copyMoveStmt clauses temporary (own 0) (own 1)) := by
    intro state stack; rfl
  have hr : ExecutesAt computer.step (own 1)
      (copyRestoreStmt clauses destination temporary (own 1) (stageLabel 0 0)) := by
    intro state stack; rfl
  have run := copy_exact clauses destination temporary (by intro h; cases h)
    (by decide) (by intro h; cases h) computer.step (own 0) (own 1) (stageLabel 0 0)
    hm hr memory (ready old m []) rfl
  simp only [ready_clauses, ready_destination, List.append_nil] at run
  have ht : Function.update (ready old m []) destination m = ready old m m := by
    funext k
    cases k with
    | inl k => rfl
    | inr k =>
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k =>
        by_cases hk : k = Arithmetic.input
        · subst k; rfl
        · simp only [ready, tapes, destination, wordTape, Function.update_apply,
            Sum.elim_inr, hk, reduceCtorEq, ite_false, Sum.inr.injEq]
  rw [ht] at run
  exact run

/-- Generic retained-copy plus canonical frame emission in this real caller. -/
theorem prepend_field (old : ParameterProgram.Stack → List Bool) (m suffix : List Bool)
    (memory : Memory) (j : Fin 4) :
    RunsExactly computer.step (cfg (stageLabel j 0) memory (ready old m suffix))
      (cfg (next j) memory
        (ready old m (Holant.Algebraic.frame (old (ParameterProgram.canonical (index j))) ++ suffix)))
      (4 * (old (ParameterProgram.canonical (index j))).length + 5) := by
  let word := old (ParameterProgram.canonical (index j))
  let copied := Function.update (ready old m suffix) staging word
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
    (stageLabel j 0) (stageLabel j 1) (stageLabel j 2) hmove hrestore memory (ready old m suffix) rfl
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
    hm hd he memory (ready old m suffix) word suffix
  have before : tapes3 (ready old m suffix) staging destination temporary word suffix [] = copied := by
    funext k
    cases k with
    | inl k => rfl
    | inr k =>
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k =>
        by_cases hk : k = Arithmetic.input
        · subst k; rfl
        · simp only [tapes3, ready, tapes, copied, staging, temporary, destination,
            wordTape, Function.update_apply, Sum.elim_inr, hk, reduceCtorEq, ite_false, Sum.inr.injEq]
  have after : tapes3 (ready old m suffix) staging destination temporary []
      (Holant.Algebraic.frame word ++ suffix) [] = ready old m (Holant.Algebraic.frame word ++ suffix) := by
    funext k
    cases k with
    | inl k => rfl
    | inr k =>
      cases k with
      | inl k => fin_cases k <;> rfl
      | inr k =>
        by_cases hk : k = Arithmetic.input
        · subst k; rfl
        · simp only [tapes3, ready, tapes, staging, temporary, destination,
            wordTape, Function.update_apply, Sum.elim_inr, hk, reduceCtorEq, ite_false, Sum.inr.injEq]
  rw [before, after] at emit
  convert cp.trans emit using 1 <;> dsimp only [word] <;> omega

/-- Literal wire produced by the four real frame emissions. -/
def serialized (old : ParameterProgram.Stack → List Bool) (m : List Bool) : List Bool :=
  Holant.Algebraic.frame (old (ParameterProgram.canonical 0)) ++
  (Holant.Algebraic.frame (old (ParameterProgram.canonical 1)) ++
  (Holant.Algebraic.frame (old (ParameterProgram.canonical 2)) ++
  (Holant.Algebraic.frame (old (ParameterProgram.canonical 3)) ++ m)))

def serializeTime (old : ParameterProgram.Stack → List Bool) (m : List Bool) : ℕ :=
  2 * m.length + 4 * ((old (ParameterProgram.canonical 0)).length +
    (old (ParameterProgram.canonical 1)).length + (old (ParameterProgram.canonical 2)).length +
    (old (ParameterProgram.canonical 3)).length) + 22

/-- Five retained copies and four frame emissions reach the actual arithmetic
entry point, with the complete input physically installed on its input stack. -/
theorem serialize (old : ParameterProgram.Stack → List Bool) (m : List Bool) (memory : Memory) :
    RunsExactly computer.step (cfg (own 0) memory (ready old m []))
      (cfg (arithmeticLabel Arithmetic.main) memory (ready old m (serialized old m)))
      (serializeTime old m) := by
  have first := initial_copy old m memory
  have h0 := prepend_field old m m memory 0
  have h1 := prepend_field old m (Holant.Algebraic.frame (old (ParameterProgram.canonical 3)) ++ m) memory 1
  have h2 := prepend_field old m
    (Holant.Algebraic.frame (old (ParameterProgram.canonical 2)) ++
      (Holant.Algebraic.frame (old (ParameterProgram.canonical 3)) ++ m)) memory 2
  have h3 := prepend_field old m
    (Holant.Algebraic.frame (old (ParameterProgram.canonical 1)) ++
      (Holant.Algebraic.frame (old (ParameterProgram.canonical 2)) ++
        (Holant.Algebraic.frame (old (ParameterProgram.canonical 3)) ++ m))) memory 3
  change RunsExactly computer.step _ (cfg (stageLabel 1 0) memory _) _ at h0
  change RunsExactly computer.step _ (cfg (stageLabel 2 0) memory _) _ at h1
  change RunsExactly computer.step _ (cfg (stageLabel 3 0) memory _) _ at h2
  change RunsExactly computer.step _ (cfg (arithmeticLabel Arithmetic.main) memory _) _ at h3
  have hi0 : index 0 = 3 := rfl
  have hi1 : index 1 = 2 := rfl
  have hi2 : index 2 = 1 := rfl
  have hi3 : index 3 = 0 := rfl
  rw [hi0] at h0
  rw [hi1] at h1
  rw [hi2] at h2
  rw [hi3] at h3
  convert (((first.trans h0).trans h1).trans h2).trans h3 using 1
  · rfl
  · unfold serializeTime; omega

def resultTapes (old : ParameterProgram.Stack → List Bool) (m output : List Bool) : Stack → List Bool :=
  tapes old m [] [] (wordTape Arithmetic.output output)

set_option maxHeartbeats 1000000 in
/-- The serialized word runs through the inlined H1 arithmetic program with
its original exact source time. Every original bank word and the clause-count
word is preserved outside that embedded arithmetic bank. -/
theorem arithmetic_run (old : ParameterProgram.Stack → List Bool) (m : List Bool)
    (memory : ParameterProgram.Memory) (x : ParameterCounts.Input) :
    RunsExactly computer.step
      (cfg (arithmeticLabel Arithmetic.main) (memory, Arithmetic.initial)
        (ready old m (ParameterCounts.inputEncoding.encode x)))
      (cfg (own 22) (memory, Arithmetic.initial)
        (resultTapes old m (ParameterCounts.outputEncoding.encode (ParameterCounts.result x))))
      (ParameterCounts.computes.outputs x).steps := by
  let input := ParameterCounts.inputEncoding.encode x
  let output := ParameterCounts.outputEncoding.encode (ParameterCounts.result x)
  have code : ∀ l, program (arithmeticLabel l) =
      MachineCall.block arithmeticMap arithmeticLabel (own 22) arithmeticState (Arithmetic.program l) := by
    intro l; rfl
  have ha : Embedded.Rel arithmeticMap arithmeticLabel (own 22) (ready old m [])
      (StateAdapter.cfg arithmeticState (none, memory) (initList Arithmetic.computer input))
      (cfg (arithmeticLabel Arithmetic.main) (memory, Arithmetic.initial) (ready old m input)) := by
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
  have hz : Embedded.Rel arithmeticMap arithmeticLabel (own 22) (ready old m [])
      (StateAdapter.cfg arithmeticState (none, memory) (haltList Arithmetic.computer output))
      (cfg (own 22) (memory, Arithmetic.initial) (resultTapes old m output)) := by
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
  have hr : (fun p => p.bind (TM2.step Arithmetic.program))^[(ParameterCounts.computes.outputs x).steps]
      (some (initList Arithmetic.computer input)) = some (haltList Arithmetic.computer output) :=
    (ParameterCounts.computes.outputs x).evals_in_steps
  exact MachineCall.run arithmeticMap arithmeticLabel (own 22) arithmeticState Arithmetic.program
    program code (none, memory) (ready old m []) _ _ _ _ _ ha hz hr

def input (source : RequestParser.Stack → List Bool) (m : ℕ) : ParameterCounts.Input :=
  (decodeNat (ParameterValidation.rawField source 0), decodeNat (ParameterValidation.rawField source 1),
    decodeNat (ParameterValidation.rawField source 2), decodeNat (ParameterValidation.rawField source 3), m)

theorem serialized_prepared (source : RequestParser.Stack → List Bool) (m : ℕ) :
    serialized (ParameterValidation.prepared source 4) (encodeNat m) =
      ParameterCounts.inputEncoding.encode (input source m) := rfl

def finished (source : RequestParser.Stack → List Bool) (m : ℕ) (memory : ParameterProgram.Memory) : Config :=
  ⟨none, (none, memory, Arithmetic.initial),
    resultTapes (ParameterValidation.prepared source 4) (encodeNat m)
      (ParameterCounts.outputEncoding.encode (ParameterCounts.result (input source m)))⟩

set_option maxHeartbeats 1000000 in
/-- Actual prepared-parameter-bank to binary counts execution. This includes
serialization, all arithmetic, all transfer/cleanup, and the caller's halt. -/
theorem run (source : RequestParser.Stack → List Bool) (m : ℕ) (memory : ParameterProgram.Memory) :
    RunsExactly computer.step
      (cfg (own 0) (memory, Arithmetic.initial)
        (ready (ParameterValidation.prepared source 4) (encodeNat m) []))
      (finished source m memory)
      (1 + ((ParameterCounts.computes.outputs (input source m)).steps +
        serializeTime (ParameterValidation.prepared source 4) (encodeNat m))) := by
  have hs := serialize (ParameterValidation.prepared source 4) (encodeNat m) (memory, Arithmetic.initial)
  rw [serialized_prepared] at hs
  have ha := arithmetic_run (ParameterValidation.prepared source 4) (encodeNat m) memory (input source m)
  have hf : computer.step
      (cfg (own 22) (memory, Arithmetic.initial)
        (resultTapes (ParameterValidation.prepared source 4) (encodeNat m)
          (ParameterCounts.outputEncoding.encode (ParameterCounts.result (input source m))))) =
      some (finished source m memory) := by rfl
  exact (hs.trans ha).trans (runsExactly_one hf)

/-- The old request bank and canonical clause word are preserved literally. -/
theorem finished_original (source : RequestParser.Stack → List Bool) (m : ℕ)
    (memory : ParameterProgram.Memory) (k : ParameterProgram.Stack) :
    (finished source m memory).stk (.inl k) = ParameterValidation.prepared source 4 k := rfl

theorem finished_clauses (source : RequestParser.Stack → List Bool) (m : ℕ)
    (memory : ParameterProgram.Memory) :
    (finished source m memory).stk clauses = encodeNat m := rfl

theorem finished_work (source : RequestParser.Stack → List Bool) (m : ℕ)
    (memory : ParameterProgram.Memory) :
    (finished source m memory).stk temporary = [] ∧
      (finished source m memory).stk staging = [] := ⟨rfl, rfl⟩

theorem finished_output (source : RequestParser.Stack → List Bool) (m : ℕ)
    (memory : ParameterProgram.Memory) :
    (finished source m memory).stk (arithmeticMap Arithmetic.output) =
      ParameterCounts.outputEncoding.encode (ParameterCounts.result (input source m)) := by
  exact wordTape_at Arithmetic.output
    (ParameterCounts.outputEncoding.encode (ParameterCounts.result (input source m)))

theorem input_fields {source : RequestParser.Stack → List Bool} {f : ProblemHeader.Fields}
    (hs : ParameterValidation.SourceFields source f) (m : ℕ) :
    input source m = ParameterCounts.fields f.epsilon f.delta m := by
  unfold input ParameterCounts.fields
  rw [ParameterValidation.rawField_eq hs 0, ParameterValidation.rawField_eq hs 1,
    ParameterValidation.rawField_eq hs 2, ParameterValidation.rawField_eq hs 3]
  rfl

theorem input_length_le (source : RequestParser.Stack → List Bool) (m n : ℕ)
    (hl : ∀ i, (ParameterValidation.rawField source i).length ≤ n) :
    (ParameterCounts.inputEncoding.encode (input source m)).length ≤
      8 * n + (encodeNat m).length + 12 := by
  rw [ParameterCounts.input_length]
  have h0 := ParameterValidation.canonical_length_le (ParameterValidation.rawField source 0)
  have h1 := ParameterValidation.canonical_length_le (ParameterValidation.rawField source 1)
  have h2 := ParameterValidation.canonical_length_le (ParameterValidation.rawField source 2)
  have h3 := ParameterValidation.canonical_length_le (ParameterValidation.rawField source 3)
  have hn0 := hl 0
  have hn1 := hl 1
  have hn2 := hl 2
  have hn3 := hl 3
  dsimp only [input]
  omega

theorem serializeTime_le (source : RequestParser.Stack → List Bool) (m n : ℕ)
    (hl : ∀ i, (ParameterValidation.rawField source i).length ≤ n) :
    serializeTime (ParameterValidation.prepared source 4) (encodeNat m) ≤
      16 * n + 2 * (encodeNat m).length + 38 := by
  unfold serializeTime
  rw [ParameterValidation.prepared_canonical, ParameterValidation.prepared_canonical,
    ParameterValidation.prepared_canonical, ParameterValidation.prepared_canonical]
  have h0 := ParameterValidation.canonical_length_le (ParameterValidation.rawField source 0)
  have h1 := ParameterValidation.canonical_length_le (ParameterValidation.rawField source 1)
  have h2 := ParameterValidation.canonical_length_le (ParameterValidation.rawField source 2)
  have h3 := ParameterValidation.canonical_length_le (ParameterValidation.rawField source 3)
  have hn0 := hl 0
  have hn1 := hl 1
  have hn2 := hl 2
  have hn3 := hl 3
  omega

/-- Binary parameter arithmetic is polynomial in physical words. This bound
never replaces a later sample-count loop by its output's bit length. -/
def timeBound (n countBits : ℕ) : ℕ :=
  16 * n + 2 * countBits + 39 + ParameterCounts.computes.time.eval (8 * n + countBits + 12)

theorem time_le (source : RequestParser.Stack → List Bool) (m n : ℕ)
    (hl : ∀ i, (ParameterValidation.rawField source i).length ≤ n) :
    1 + ((ParameterCounts.computes.outputs (input source m)).steps +
      serializeTime (ParameterValidation.prepared source 4) (encodeNat m)) ≤
      timeBound n (encodeNat m).length := by
  have hc := (ParameterCounts.computes.outputs (input source m)).steps_le_m
  have hm := natPolynomial_eval_mono ParameterCounts.computes.time (input_length_le source m n hl)
  have hs := serializeTime_le source m n hl
  unfold timeBound
  omega

theorem local_budget (l : Fin 23) : TM2Cost.budget (localProgram l) ≤ 10 := by
  fin_cases l <;> decide

theorem program_budget (l : Label) :
    TM2Cost.budget (program l) ≤ 10 + Arithmetic.primitiveBudget := by
  cases l with
  | inl l => exact (local_budget l).trans (Nat.le_add_right _ _)
  | inr l =>
    change TM2Cost.budget (Embedded.block arithmeticMap arithmeticLabel (own 22)
      (StateAdapter.block arithmeticState (Arithmetic.program l))) ≤ _
    rw [Embedded.statement_budget, StateAdapter.statement_budget]
    exact (Arithmetic.program_budget_le l).trans (Nat.le_add_left _ _)

set_option maxHeartbeats 1000000 in
/-- Primitive accumulation covers the serializer and the inlined arithmetic
in the very same caller program. -/
theorem bit_cost (source : RequestParser.Stack → List Bool) (m n : ℕ)
    (memory : ParameterProgram.Memory)
    (hl : ∀ i, (ParameterValidation.rawField source i).length ≤ n) :
    (Primitive.run program
      (1 + ((ParameterCounts.computes.outputs (input source m)).steps +
        serializeTime (ParameterValidation.prepared source 4) (encodeNat m)))
      (some (cfg (own 0) (memory, Arithmetic.initial)
        (ready (ParameterValidation.prepared source 4) (encodeNat m) [])))).1 ≤
      (10 + Arithmetic.primitiveBudget) * timeBound n (encodeNat m).length := by
  have hc := Primitive.execution_cost program (10 + Arithmetic.primitiveBudget) program_budget
    _ _ _ (run source m memory)
  exact hc.2.trans (Nat.mul_le_mul_left _ (time_le source m n hl))

end
end Counting.Algorithm.KarpLubyRequest.ParameterCountsBank


