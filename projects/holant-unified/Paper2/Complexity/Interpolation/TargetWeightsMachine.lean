import Paper2.Complexity.Interpolation.TargetWeightsBounds

/-! An actual finite target-interpolation machine on a reachable transcript
context.  The source/context bytes remain in the input encoding, so arithmetic
certificates and the clock are measured before cancellation of oracle values.
Every runtime count/list producer below is itself an actual `Computes`. -/
namespace Paper2.Complexity.Interpolation.TargetWeights
open Turing Computability Holant.Algebraic
open Holant.Complexity Holant.Complexity.BinaryCompose
open Holant.Complexity.FixedFieldMachines
open Holant.Complexity.BinaryInterpolation
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

variable {A D K : Type} [Field K] [Algebra ℚ K] [Fintype D] {n : ℕ}

/-- Data needed from a literal reachable oracle transcript.  The proof fields
certify the answers; neither the finite program nor its input reads proofs. -/
structure Data (F : FixedField K n) (base : D → Fin n → ℚ) (ea : Encoding A Bool) where
  gamma : K
  target : K
  unit : D
  unit_exact : F.decode (base unit) = 1
  literal_bound : ∀ a, ArithmeticSize.Bound (fun d => F.decode (base d)) 1
    (WeightFormulas.coefficients gamma target a)
  count : A → ℕ
  answers : (r : A) → Fin (count r+1) → K
  countComputes : Computes ea WeightCompiler.unary count
  answersComputes : Computes ea (stackEncoding F.encoding) (fun r => List.ofFn (answers r))
  count_le : ∀ r, count r ≤ (ea.encode r).length
  answerBudget : Polynomial ℕ
  answer_bound : ∀ r i, ArithmeticSize.Bound (fun d => F.decode (base d))
    (answerBudget.eval (ea.encode r).length) (answers r i)

variable {F : FixedField K n} {base : D → Fin n → ℚ} {ea : Encoding A Bool}
variable (d : Data F base ea)

def prepare : Computes ea
    (pairEncoding (codeEncoding WeightCompiler.labels) (stackEncoding F.encoding))
    (fun r => (reference (d.count r),List.ofFn (d.answers r))) :=
  pairComputes (d.countComputes.andThen compiler) d.answersComputes

def widthPolynomial : Polynomial ℕ :=
  (RingFormulaMachine.widthPolynomial F base).comp (structuralPolynomial d.answerBudget)

def instructionPolynomial : Polynomial ℕ :=
  let W := widthPolynomial d
  let H := structuralPolynomial d.answerBudget
  let P := fieldProviders F
  P.add.time.comp (3*W+1)+P.mul.time.comp (3*W+1)+14*W+18+
    (2*W+4)*Polynomial.C (2^18)+3+
    Polynomial.C (2*(RingFormulaMachine.labelBound WeightCompiler.labels+6))+
    4*((2*W+2)*H+1)+9

def interpreterTime : Polynomial ℕ :=
  4*(prepare d).outputBound.bound+6+codePolynomial*instructionPolynomial d

def arithmeticTime : Polynomial ℕ :=
  interpreterTime d+8*widthPolynomial d+12+
    (DivisionStack.computes F).time.comp (4*widthPolynomial d+5)

def timePolynomial : Polynomial ℕ :=
  (prepare d).time+2*((prepare d).outputBound.bound+1)+arithmeticTime d

def arithmetic := (interpreter F d.gamma d.target).compose (DivisionStack.computes F).machine
def machine := (prepare d).machine.compose (arithmetic d)

@[simp] theorem width_eval (N : ℕ) : (widthPolynomial d).eval N =
    ArithmeticSize.bitBound F base ((structuralPolynomial d.answerBudget).eval N) := by
  classical
  simp [widthPolynomial,RingFormulaMachine.width_eval]

@[simp] theorem instruction_eval (N : ℕ) : (instructionPolynomial d).eval N =
    Interpreter.instructionBound (RingFormulaMachine.labelBound WeightCompiler.labels)
      F.encoding (fieldProviders F) ((widthPolynomial d).eval N)
      ((structuralPolynomial d.answerBudget).eval N) := by
  simp [instructionPolynomial,Interpreter.instructionBound,Kernels.timeBound]

theorem certified_input (r : A) :
    Certified F.encoding (RingFormulaMachine.coefficients F
      (literalCoordinates F d.gamma d.target))
      ((widthPolynomial d).eval (ea.encode r).length)
      ((structuralPolynomial d.answerBudget).eval (ea.encode r).length)
      (reference (d.count r)) (List.ofFn (d.answers r))
      [(resultPair d.gamma d.target (d.count r) (d.answers r)).1,
       (resultPair d.gamma d.target (d.count r) (d.answers r)).2]
      (trace d.gamma d.target (d.count r) (d.answers r)) := by
  rw [width_eval]
  exact certified F base d.unit d.unit_exact d.gamma d.target d.literal_bound
    d.answerBudget (d.count r) (ea.encode r).length (d.count_le r) (d.answers r)
    (d.answer_bound r)

theorem result_length (r : A) :
    ((DivisionStack.encoding F).encode
      (resultPair d.gamma d.target (d.count r) (d.answers r))).length ≤
      4*(widthPolynomial d).eval (ea.encode r).length+5 := by
  have h := (certified_input d r).output_width
  have h₁ := h (resultPair d.gamma d.target (d.count r) (d.answers r)).1 (by simp)
  have h₂ := h (resultPair d.gamma d.target (d.count r) (d.answers r)).2 (by simp)
  rw [DivisionStack.encoding_length]
  omega

theorem component_lengths (r : A) :
    let L := (prepare d).outputBound.bound.eval (ea.encode r).length
    ((codeEncoding WeightCompiler.labels).encode (reference (d.count r))).length ≤ L ∧
      ((stackEncoding F.encoding).encode (List.ofFn (d.answers r))).length ≤ L := by
  have h := (prepare d).outputBound.length_le r
  rw [pairEncoding_length] at h
  dsimp only [Prod.fst,Prod.snd] at h
  dsimp only
  omega

def interpreter_outputs (r : A) :
    TM2OutputsInTime (interpreter F d.gamma d.target).computer
      ((pairEncoding (codeEncoding WeightCompiler.labels) (stackEncoding F.encoding)).encode
        (reference (d.count r),List.ofFn (d.answers r)))
      (some ((DivisionStack.encoding F).encode
        (resultPair d.gamma d.target (d.count r) (d.answers r))))
      ((interpreterTime d).eval (ea.encode r).length) := by
  let hex := StackInputInterpreter.execute WeightCompiler.labels
    (RingFormulaMachine.labelBound WeightCompiler.labels) F.encoding _
    (RingFormulaMachine.literals F (literalCoordinates F d.gamma d.target))
    (fieldProviders F) (RingFormulaMachine.label_le WeightCompiler.labels) (certified_input d r)
  let t := hex.choose
  have ht := hex.choose_spec.1
  have hr := hex.choose_spec.2
  refine { steps := t, evals_in_steps := hr, steps_le_m := ?_ }
  have hlen := component_lengths d r
  have hc : (reference (d.count r)).length ≤ codePolynomial.eval (ea.encode r).length := by
    calc
      _ ≤ codeBound (d.count r) := reference_length_le (d.count r)
      _ = codePolynomial.eval (d.count r) := (codePolynomial_eval (d.count r)).symm
      _ ≤ _ := natPolynomial_eval_mono codePolynomial (d.count_le r)
  have hm := Nat.mul_le_mul_right ((instructionPolynomial d).eval (ea.encode r).length) hc
  rw [instruction_eval] at hm
  simp only [interpreterTime,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,instruction_eval]
  omega

def arithmetic_outputs (r : A) :
    TM2OutputsInTime (arithmetic d).computer
      ((pairEncoding (codeEncoding WeightCompiler.labels) (stackEncoding F.encoding)).encode
        (reference (d.count r),List.ofFn (d.answers r)))
      (some (F.encoding.encode (value d.gamma d.target (d.count r) (d.answers r))))
      ((arithmeticTime d).eval (ea.encode r).length) := by
  let first := interpreter_outputs d r
  let last := (DivisionStack.computes F).outputs
    (resultPair d.gamma d.target (d.count r) (d.answers r))
  let all := BinaryCompose.Machine.compose_correct (interpreter F d.gamma d.target)
    (DivisionStack.computes F).machine _ _ _ _ _ first last
  refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
  have ht := all.steps_le_m
  have hs := result_length d r
  have hd := natPolynomial_eval_mono (DivisionStack.computes F).time hs
  simp only [arithmeticTime,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_comp]
  omega

/-- The full finite TM2: generate bytecode, collect the runtime answer list,
run the physical fixed-field stack interpreter, and perform its final genuine
field division.  The explicit clock is polynomial in the retained context. -/
def evaluatesComputes : Computes ea F.encoding
    (fun r => value d.gamma d.target (d.count r) (d.answers r)) where
  machine := machine d
  time := timePolynomial d
  outputs r := by
    let first := (prepare d).outputs r
    let last := arithmetic_outputs d r
    let all := BinaryCompose.Machine.compose_correct (prepare d).machine (arithmetic d)
      _ _ _ _ _ first last
    refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
    have ht := all.steps_le_m
    have hs := (prepare d).outputBound.length_le r
    simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
      Polynomial.eval_ofNat,Polynomial.eval_one]
    omega

theorem evaluates_inFP : InFP ea F.encoding
    (fun r => value d.gamma d.target (d.count r) (d.answers r)) :=
  (evaluatesComputes d).inFP

end
end Paper2.Complexity.Interpolation.TargetWeights
