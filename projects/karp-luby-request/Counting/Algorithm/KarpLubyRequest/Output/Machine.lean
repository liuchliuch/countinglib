import Counting.Algorithm.KarpLubyRequest.Output.Routines
import Holant.Complexity.GraphPreprocessing.Primitive

/-! A clean finite bit-stack machine returning the original R1 rational codec.
The cubic includes input extraction, the existing binary gcd/two divisions,
component extraction, reversals, integer sign emission and final framing. -/
namespace Counting.Algorithm.KarpLubyRequest.Output
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open RationalArithmetic
open Counting.Algorithm.KarpLuby
open Program

/-- Exact source-transition count, including the final halted configuration. -/
def time (a s : ℕ) : ℕ :=
  2 * ((encodeNat a).length + 1) + (2 * (encodeNat s).length + 2) +
    Normalization.normalizeTime false a s +
    ((parityWord (numerator a s)).length + (encodeNat (denominator a s)).length +
      2 * (encodeNat (numerator a s)).length + 7)

def timeBound (N : ℕ) : ℕ := 200 * (N + 1) ^ 3

theorem time_le (a s : ℕ) : time a s ≤ timeBound (input a s).length := by
  have hn := numerator_length_le a s
  have hd := denominator_length_le a s
  have hp := parityWord_length (numerator a s)
  have hi := input_length a s
  have hc : (encodeNat a).length + (encodeNat s).length + 1 ≤ (input a s).length + 1 := by omega
  have ht := (Normalization.normalizeTime_le false a s).trans
    (Nat.mul_le_mul_left 128 (Nat.pow_le_pow_left hc 3))
  unfold time timeBound
  nlinarith [Nat.zero_le ((input a s).length ^ 2), Nat.zero_le ((input a s).length ^ 3)]

theorem initial_eq (word : List Bool) :
    cfg (ph .inputScan) initial (bank [] [] [] word) = initList computer word := by
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

theorem halt_eq (word : List Bool) :
    (⟨none, (none, initial), bank [] word [] []⟩ : computer.Cfg) = haltList computer word := by
  congr 1
  funext k
  cases k with
  | inl k => cases k with
    | inl k => cases k <;> rfl
    | inr k => cases k <;> rfl
  | inr k => cases k <;> rfl

/-- Exact cost from two prepared canonical component stacks. -/
def componentTime (a s : ℕ) : ℕ :=
  Normalization.normalizeTime false a s +
    ((parityWord (numerator a s)).length + (encodeNat (denominator a s)).length +
      2 * (encodeNat (numerator a s)).length + 7)

/-- A caller that already holds separate natural words can enter here. The
normalizer and serializer are the identical actual instructions of `computer`. -/
theorem prepared_components (a s : ℕ) :
    RunsExactly computer.step
      (cfg (.inl (Normalization.ph .start)) initial (bank (encodeNat a) (encodeNat s) [] []))
      (haltList computer (Encoding.encodeOutput ((a : ℚ) / s))) (componentTime a s) := by
  have h := (normalize_run a s).trans (serialize_run (numerator a s) (denominator a s))
  rw [← output_eq, halt_eq] at h
  convert h using 1 <;> unfold componentTime <;> omega

theorem componentTime_le (a s : ℕ) : componentTime a s ≤ timeBound (input a s).length := by
  have h : componentTime a s ≤ time a s := by unfold componentTime time; omega
  exact h.trans (time_le a s)

/-- Complete actual run on the original prepared natural-pair input. In
particular, a=0 and s=0 produce the literal signed/framed rational zero. -/
theorem prepared_run (a s : ℕ) :
    RunsExactly computer.step (initList computer (input a s))
      (haltList computer (Encoding.encodeOutput ((a : ℚ) / s))) (time a s) := by
  have h := (((input_frame_run a s).trans (denominator_run (encodeNat a) (encodeNat s))).trans
    (normalize_run a s)).trans (serialize_run (numerator a s) (denominator a s))
  rw [initial_eq, ← output_eq, halt_eq] at h
  convert h using 1 <;> unfold time <;> omega

/-- This timed witness measures transitions of the displayed finite machine. -/
noncomputable def outputs (a s : ℕ) :
    TM2OutputsInTime computer (input a s) (some (Encoding.encodeOutput ((a : ℚ) / s)))
      (timeBound (input a s).length) where
  steps := time a s
  evals_in_steps := prepared_run a s
  steps_le_m := time_le a s

/-- A linear final-word bound, after gcd reduction. -/
theorem output_length_le (a s : ℕ) :
    (Encoding.encodeOutput ((a : ℚ) / s)).length ≤ (input a s).length + 7 := by
  have hn := numerator_length_le a s
  have hd := denominator_length_le a s
  rw [output_eq, List.length_append, List.length_append, Encoding.frame_length]
  have hi := input_length a s
  simp only [signPrefix, List.length_cons, List.length_nil]
  omega

/-- The same run under the actual primitive-instruction interpreter. -/
theorem primitive_cost (a s : ℕ) :
    (Primitive.run program (time a s) (some (initList computer (input a s)))).2 =
      some (haltList computer (Encoding.encodeOutput ((a : ℚ) / s))) ∧
    (Primitive.run program (time a s) (some (initList computer (input a s)))).1 ≤
      12 * timeBound (input a s).length := by
  have h := Primitive.execution_cost program 12 statement_budget (time a s) _ _ (prepared_run a s)
  exact ⟨h.1, h.2.trans (Nat.mul_le_mul_left 12 (time_le a s))⟩

/-- A returning call keeps every caller stack outside these fourteen stacks. -/
theorem caller_run {J R : Type} [DecidableEq J] (e : Stack ↪ J)
    (labels : Label → R) (ret : R)
    (caller : R → TM2.Stmt (fun _ : J => Bool) R State)
    (code : ∀ l, caller (labels l) = Embedded.block e labels ret (program l))
    (a s : ℕ) (start : TM2.Cfg (fun _ : J => Bool) R State) (frame : J → List Bool)
    (hstart : Embedded.Rel e labels ret frame (initList computer (input a s)) start) :
    ∃ ending, (fun p => p.bind (TM2.step caller))^[time a s] (some start) = some ending ∧
      ending.l = some ret ∧ ending.stk (e (ex .den)) = Encoding.encodeOutput ((a : ℚ) / s) ∧
      (∀ k, k ≠ ex .den → ending.stk (e k) = []) ∧
      (∀ j, (∀ k, j ≠ e k) → ending.stk j = frame j) := by
  have hr := prepared_run a s
  rw [← halt_eq] at hr
  obtain ⟨ending, run, rel⟩ := Embedded.run e labels ret program caller code _ _ start frame
    (time a s) hstart hr
  refine ⟨ending, run, rel.1, rel.2.2.1 (ex .den), ?_, rel.2.2.2⟩
  intro k hk
  have h := rel.2.2.1 k
  cases k with
  | inl k => exact h
  | inr k => cases k <;> first | exact False.elim (hk rfl) | exact h

/-- Returning version of the two-stack entry. Placement of the two words
is a concrete initial configuration requirement; output equality is proved. -/
theorem components_caller_run {J R : Type} [DecidableEq J] (e : Stack ↪ J)
    (labels : Label → R) (ret : R)
    (caller : R → TM2.Stmt (fun _ : J => Bool) R State)
    (code : ∀ l, caller (labels l) = Embedded.block e labels ret (program l))
    (a s : ℕ) (start : TM2.Cfg (fun _ : J => Bool) R State) (frame : J → List Bool)
    (hstart : Embedded.Rel e labels ret frame
      (cfg (.inl (Normalization.ph .start)) initial (bank (encodeNat a) (encodeNat s) [] [])) start) :
    ∃ ending, (fun p => p.bind (TM2.step caller))^[componentTime a s] (some start) = some ending ∧
      ending.l = some ret ∧ ending.stk (e (ex .den)) = Encoding.encodeOutput ((a : ℚ) / s) ∧
      (∀ k, k ≠ ex .den → ending.stk (e k) = []) ∧
      (∀ j, (∀ k, j ≠ e k) → ending.stk j = frame j) := by
  have hr := prepared_components a s
  rw [← halt_eq] at hr
  obtain ⟨ending, run, rel⟩ := Embedded.run e labels ret program caller code _ _ start frame
    (componentTime a s) hstart hr
  refine ⟨ending, run, rel.1, rel.2.2.1 (ex .den), ?_, rel.2.2.2⟩
  intro k hk
  have h := rel.2.2.1 k
  cases k with
  | inl k => exact h
  | inr k => cases k <;> first | exact False.elim (hk rfl) | exact h

/-- Explicit bridge to the frozen estimator, now in its original final codec. -/
theorem estimator_run {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (tape : CoinTape (KarpLuby.Program.randomBitBudget cs s g)) :
    RunsExactly computer.step
      (initList computer (input (KarpLubyMachine.NumeratorMedian.estimate cs s g tape).value s))
      (haltList computer (Encoding.encodeOutput (KarpLuby.Program.estimate cs s g tape)))
      (time (KarpLubyMachine.NumeratorMedian.estimate cs s g tape).value s) := by
  have h := prepared_run (KarpLubyMachine.NumeratorMedian.estimate cs s g tape).value s
  rw [← KarpLubyMachine.NumeratorMedian.estimate_refines] at h
  exact h

/-- Request parameters only specialize the proved physical input-size bound;
this is the output postprocessor, not the whole-request FPRAS machine. -/
noncomputable def requestOutputs {n : ℕ} (f : DNF.Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (KarpLuby.Program.requestedBudget f epsilon delta)) :
    TM2OutputsInTime computer
      (input (KarpLubyMachine.NumeratorMedian.estimate (DNF.normalizeFormula f)
        (KarpLuby.Program.requestedSamples (DNF.normalizeFormula f) epsilon)
        (KarpLuby.Program.requestedGroups delta) tape).value
        (KarpLuby.Program.requestedSamples (DNF.normalizeFormula f) epsilon))
      (some (Encoding.encodeOutput (KarpLuby.Program.run f epsilon delta tape)))
      (200 * (5 * f.length.size + 6 * epsilon.den.size + 2 * n + 38) ^ 3) := by
  let cs := DNF.normalizeFormula f
  let s := KarpLuby.Program.requestedSamples cs epsilon
  let g := KarpLuby.Program.requestedGroups delta
  let a := (KarpLubyMachine.NumeratorMedian.estimate cs s g tape).value
  refine { steps := time a s, evals_in_steps := estimator_run cs s g tape, steps_le_m := ?_ }
  have ha : a.size ≤ s.size + cs.length.size + n + 2 :=
    KarpLubyMachine.NumeratorMedian.estimate_size_le cs s g tape
  have hs : s.size ≤ cs.length.size + 2 * epsilon.den.size + 10 :=
    KarpLuby.ResourceBounds.samples_size_le cs.length epsilon
  have hm : cs.length.size ≤ f.length.size :=
    Nat.size_le_size (KarpLuby.ResourceBounds.normalized_length_le f)
  have he : (input a s).length + 1 ≤ 5 * f.length.size + 6 * epsilon.den.size + 2 * n + 38 := by
    rw [input_length, Holant.Algebraic.encodeNat_length, Holant.Algebraic.encodeNat_length]
    omega
  exact (time_le a s).trans (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left he 3))

end Counting.Algorithm.KarpLubyRequest.Output
