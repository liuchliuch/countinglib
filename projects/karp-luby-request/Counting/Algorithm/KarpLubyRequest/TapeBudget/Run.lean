import Counting.Algorithm.KarpLubyRequest.TapeBudget.Bank

/-!
# Exact budget-check execution and physical-size bounds

The two-transition zero-mass branch never enters serialization or arithmetic.
The nonzero branch preserves all four supplied words, computes the length
comparison using the real source program, clears its answer stack, and returns
the validity bit. The polynomial below bounds that execution, not the later
number of samples. Successful positive counts are separately bounded by the
length of the physically supplied random tape.
-/
namespace Counting.Algorithm.KarpLubyRequest.TapeBudget.Bank
noncomputable section
open Turing Computability Holant.Complexity StackProtocol BinaryCompose FixedFieldMachines GraphPreprocessing

/-- Canonical arithmetic parameters with the original random tape verbatim. -/
def prepared (x : Arithmetic.Input) : Fin 4 → List Bool :=
  ![encodeNat x.1, encodeNat x.2.1, encodeNat x.2.2.1, x.2.2.2]

def finished (old : Fin 4 → List Bool) (valid zeroMass : Bool) : Config :=
  ⟨none, (none, (valid, zeroMass), Engine.initial), ready old []⟩

theorem serialized_prepared (x : Arithmetic.Input) :
    serialized (prepared x) = Arithmetic.inputEncoding.encode x := rfl

theorem dispatch_zero (old : Fin 4 → List Bool) (status : Status) (hm : old 2 = []) :
    computer.step (cfg (own 0) (status, Engine.initial) (ready old [])) =
      some (cfg (own 1) (status, Engine.initial) (ready old [])) := by
  change some (TM2.stepAux dispatch (none, status, Engine.initial) (ready old [])) = _
  simp [dispatch, TM2.stepAux, ready_original, hm, cfg]

theorem dispatch_positive (old : Fin 4 → List Bool) (status : Status) (hm : old 2 ≠ []) :
    computer.step (cfg (own 0) (status, Engine.initial) (ready old [])) =
      some (cfg (own 2) (status, Engine.initial) (ready old [])) := by
  cases hw : old 2 with
  | nil => exact False.elim (hm hw)
  | cons bit rest =>
    change some (TM2.stepAux dispatch (none, status, Engine.initial) (ready old [])) = _
    simp [dispatch, TM2.stepAux, ready_original, hw, cfg]

/-- Only the first random-tape cell is inspected on the zero branch. -/
theorem zero_finish (old : Fin 4 → List Bool) (status : Status) :
    computer.step (cfg (own 1) (status, Engine.initial) (ready old [])) =
      some (finished old (decide (old 3 = [])) true) := by
  change some (TM2.stepAux zeroCase (none, status, Engine.initial) (ready old [])) = _
  cases hw : old 3 with
  | nil => simp [zeroCase, TM2.stepAux, ready_original, hw, finished]
  | cons bit rest => simp [zeroCase, TM2.stepAux, ready_original, hw, finished]

/-- The zero-mass branch does not depend on the sizes or numeric values of the
sample/group words, and does not traverse even a nonempty rejected tape. -/
theorem zero_run (old : Fin 4 → List Bool) (status : Status) (hm : old 2 = []) :
    RunsExactly computer.step (cfg (own 0) (status, Engine.initial) (ready old []))
      (finished old (decide (old 3 = [])) true) 2 :=
  (runsExactly_one (dispatch_zero old status hm)).trans (runsExactly_one (zero_finish old status))

theorem clear_answer (old : Fin 4 → List Bool) (answer : Bool) :
    Function.update (resultTapes old [answer]) (engineMap Engine.output) [] = ready old [] := by
  funext k
  cases k with
  | inl k => rfl
  | inr k =>
    cases k with
    | inl k => fin_cases k <;> rfl
    | inr k =>
      by_cases hk : k = Engine.output
      · subst k
        change Function.update (resultTapes old [answer]) (engineMap Engine.output) []
          (engineMap Engine.output) = wordTape Engine.input [] Engine.output
        rw [Function.update_self]
        simp only [wordTape, Function.update_apply, ite_self]
      · simp only [resultTapes, ready, tapes, engineMap, wordTape, Function.update_apply,
          Sum.elim_inr, hk, reduceCtorEq, ite_false, Sum.inr.injEq, ite_self]

/-- Consume the unique Boolean output of the arithmetic call and halt with
all arithmetic stacks empty. -/
theorem finish_answer (old : Fin 4 → List Bool) (status : Status) (answer : Bool) :
    computer.step (cfg (own 19) (status, Engine.initial) (resultTapes old [answer])) =
      some (finished old answer false) := by
  have ho : resultTapes old [answer] (engineMap Engine.output) = [answer] :=
    wordTape_at Engine.output [answer]
  change some (TM2.stepAux finish (none, status, Engine.initial) (resultTapes old [answer])) = _
  simp [finish, TM2.stepAux, ho, clear_answer, finished]

theorem canonical_mass_nonempty (x : Arithmetic.Input) (hm : x.2.2.1 ≠ 0) :
    prepared x 2 ≠ [] := by
  intro h
  have hc : encodingNatBool.encode x.2.2.1 = encodingNatBool.encode 0 := h
  exact hm (encodingNatBool.encode_injective hc)

theorem valid_zero (s g : ℕ) (tape : List Bool) :
    Arithmetic.valid (s, g, 0, tape) = decide (tape = []) := by
  change decide (tape.length = g * (s * Nat.size 0)) = decide (tape = [])
  simp

/-- The exact positive-branch cost includes the dispatch, all retained copies,
framing, all arithmetic-source transitions, and final answer removal/halt. -/
theorem positive_run (x : Arithmetic.Input) (status : Status) (hm : x.2.2.1 ≠ 0) :
    RunsExactly computer.step (cfg (own 0) (status, Engine.initial) (ready (prepared x) []))
      (finished (prepared x) (Arithmetic.valid x) false)
      (1 + ((Arithmetic.computes.outputs x).steps + (serializeTime (prepared x) + 1))) := by
  have hd := runsExactly_one (dispatch_positive (prepared x) status (canonical_mass_nonempty x hm))
  have hs := serialize (prepared x) (status, Engine.initial)
  rw [serialized_prepared] at hs
  have ha := arithmetic_run (prepared x) status x
  have hf := runsExactly_one (finish_answer (prepared x) status (Arithmetic.valid x))
  exact ((hd.trans hs).trans ha).trans hf

def steps (x : Arithmetic.Input) : ℕ :=
  if x.2.2.1 = 0 then 2
  else 1 + ((Arithmetic.computes.outputs x).steps + (serializeTime (prepared x) + 1))

def outcome (x : Arithmetic.Input) : Status := (Arithmetic.valid x, decide (x.2.2.1 = 0))

/-- Complete operational contract on all canonical numeric parameters and all
Boolean tapes. Positivity of the counts is not an input validity assumption. -/
theorem run (x : Arithmetic.Input) (status : Status) :
    RunsExactly computer.step (cfg (own 0) (status, Engine.initial) (ready (prepared x) []))
      (finished (prepared x) (outcome x).1 (outcome x).2) (steps x) := by
  rcases x with ⟨s, g, m, tape⟩
  by_cases hm : m = 0
  · subst m
    change RunsExactly computer.step
      (cfg (own 0) (status, Engine.initial) (ready (prepared (s, g, 0, tape)) []))
      (finished (prepared (s, g, 0, tape)) (Arithmetic.valid (s, g, 0, tape)) true) 2
    rw [valid_zero]
    exact zero_run (prepared (s, g, 0, tape)) status rfl
  · have h := positive_run (s, g, m, tape) status hm
    simpa only [steps, outcome, hm, ↓reduceIte, decide_false] using h

/-- Every original word, including all random bits, is preserved literally. -/
theorem finished_original (old : Fin 4 → List Bool) (valid zeroMass : Bool) (i : Fin 4) :
    (finished old valid zeroMass).stk (original i) = old i := rfl

theorem finished_work (old : Fin 4 → List Bool) (valid zeroMass : Bool) (k : Fin 2 ⊕ Engine.K) :
    (finished old valid zeroMass).stk (.inr k) = [] := by
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k =>
    change wordTape Engine.input [] k = []
    simp only [wordTape, Function.update_apply, ite_self]

/-- Physical input-word size before any serializer has run. -/
def physicalSize (x : Arithmetic.Input) : ℕ :=
  (encodeNat x.1).length + (encodeNat x.2.1).length +
    (encodeNat x.2.2.1).length + x.2.2.2.length

def timeBound (n : ℕ) : ℕ := 4 * n + 19 + Arithmetic.computes.time.eval (2 * n + 3)

noncomputable def timePolynomial : Polynomial ℕ :=
  4 * Polynomial.X + 19 + Arithmetic.computes.time.comp (2 * Polynomial.X + 3)

theorem timePolynomial_eval (n : ℕ) : timePolynomial.eval n = timeBound n := by
  simp only [timePolynomial, timeBound, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_ofNat, Polynomial.eval_X, Polynomial.eval_comp]

theorem input_length_le (x : Arithmetic.Input) :
    (Arithmetic.inputEncoding.encode x).length ≤ 2 * physicalSize x + 3 := by
  rw [Arithmetic.input_length]
  unfold physicalSize
  omega

theorem serializeTime_le (x : Arithmetic.Input) :
    serializeTime (prepared x) ≤ 4 * physicalSize x + 17 := by
  change 2 * x.2.2.2.length +
    4 * ((encodeNat x.1).length + (encodeNat x.2.1).length + (encodeNat x.2.2.1).length) + 17 ≤ _
  unfold physicalSize
  omega

theorem steps_le (x : Arithmetic.Input) : steps x ≤ timeBound (physicalSize x) := by
  by_cases hm : x.2.2.1 = 0
  · simp only [steps, hm, ↓reduceIte, timeBound]; omega
  · have hc := (Arithmetic.computes.outputs x).steps_le_m
    have hp := natPolynomial_eval_mono Arithmetic.computes.time (input_length_le x)
    have hs := serializeTime_le x
    simp only [steps, hm, ↓reduceIte, timeBound]
    omega

theorem local_budget (l : Fin 20) : TM2Cost.budget (localProgram l) ≤ 10 := by
  fin_cases l <;> decide

theorem program_budget (l : Label) : TM2Cost.budget (program l) ≤ 10 + Engine.primitiveBudget := by
  cases l with
  | inl l => exact (local_budget l).trans (Nat.le_add_right _ _)
  | inr l =>
    change TM2Cost.budget (MachineCall.block engineMap engineLabel (own 19)
      engineState (Engine.program l)) ≤ _
    rw [MachineCall.budget]
    exact (Engine.program_budget_le l).trans (Nat.le_add_left _ _)

set_option maxHeartbeats 1000000 in
/-- Actual measured primitive execution, with the same full-bank endpoint. -/
theorem bit_cost (x : Arithmetic.Input) (status : Status) :
    (Primitive.run program (steps x)
      (some (cfg (own 0) (status, Engine.initial) (ready (prepared x) [])))).2 =
        some (finished (prepared x) (outcome x).1 (outcome x).2) ∧
    (Primitive.run program (steps x)
      (some (cfg (own 0) (status, Engine.initial) (ready (prepared x) [])))).1 ≤
        (10 + Engine.primitiveBudget) * timeBound (physicalSize x) := by
  have hc := Primitive.execution_cost program (10 + Engine.primitiveBudget) program_budget
    _ _ _ (run x status)
  exact ⟨hc.1, hc.2.trans (Nat.mul_le_mul_left _ (steps_le x))⟩

/-- Zero mass gives a constant transition bound independently of even enormous
sample/group counts; no encoded arithmetic-source certificate is invoked. -/
theorem zero_steps (s g : ℕ) (tape : List Bool) : steps (s, g, 0, tape) = 2 := by
  simp only [steps, ↓reduceIte]

/-- The semantic budget is the original R1 budget, with no rounding or padded
random cells introduced by this calling convention. -/
theorem valid_program {n : ℕ} (cs : List (Counting.Algorithm.KarpLuby.DNF.Clause n))
    (s g : ℕ) (tape : List Bool) :
    Arithmetic.valid (s, g, Counting.Algorithm.KarpLuby.Program.totalMass cs, tape) =
      decide (tape.length = Counting.Algorithm.KarpLuby.Program.randomBitBudget cs s g) := rfl

/-- Once a positive-width tape passes the exact gate, materializing either
positive loop count cannot outrun the physical input tape length. -/
theorem counts_le_tape (s g m : ℕ) (tape : List Bool)
    (hs : 0 < s) (hg : 0 < g) (hm : 0 < m)
    (hv : Arithmetic.valid (s, g, m, tape) = true) :
    s ≤ tape.length ∧ g ≤ tape.length := by
  have hw : 0 < Nat.size m := Nat.size_pos.mpr hm
  have ht : tape.length = g * (s * Nat.size m) := of_decide_eq_true hv
  constructor <;> rw [ht]
  · have hsw : s ≤ s * Nat.size m := by nlinarith
    have hmul : s * Nat.size m ≤ g * (s * Nat.size m) := by nlinarith
    exact hsw.trans hmul
  · have hprod : 1 ≤ s * Nat.size m := by nlinarith
    nlinarith

end
end Counting.Algorithm.KarpLubyRequest.TapeBudget.Bank
