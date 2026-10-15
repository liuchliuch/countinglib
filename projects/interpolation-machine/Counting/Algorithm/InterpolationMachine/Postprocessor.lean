import Counting.Algorithm.InterpolationMachine.Semantics
import Holant.Proofs.BinaryInterpolation.PostprocessBounds
import Holant.Complexity.BinaryInterpolation.DivisionStack

/-!
# Actual fixed-schedule postprocessing of canonical exact-field answers

This is the existing stack interpreter followed by the existing field division
machine. The input contains physically serialized bytecode and ordered answers.
The answer-height certificate is a mathematical bound, not an executable oracle
or an assumed machine. Graph.lean derives that certificate from actual queries.
-/
namespace Counting.Algorithm.InterpolationMachine

open Turing Computability Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose Holant.Complexity.BinaryInterpolation
open Holant.Complexity.FixedFieldMachines
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine

namespace Postprocessor
namespace PB
export Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds
  (budget trace trace_bound reference_run execute_reference)
end PB
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K D : Type} [Field K] [Algebra ℚ K] [Fintype D] {n : ℕ}
variable (F : FixedField K n) (gamma rho : K)

abbrev codeEncoding := StackProgram.codeEncoding WeightCompiler.labels
abbrev inputEncoding := pairEncoding codeEncoding (stackEncoding F.encoding)
abbrev literals := RingFormulaMachine.literals F
  (fun a => F.decode.symm (WeightFormulas.coefficients gamma rho a))
abbrev labelBound := RingFormulaMachine.labelBound WeightCompiler.labels
abbrev interpreter := StackInputInterpreter.machine
  (Kernels.machine (literals F gamma rho) (fieldProviders F)) WeightCompiler.labels labelBound
/-- One fixed Boolean-stack TM2 handles every degree and every canonical answer list. -/
abbrev machine := (interpreter F gamma rho).compose (DivisionStack.computes F).machine

/-- Every internal stack is Boolean; this is stronger than finite support. -/
@[instance_reducible] def finiteAlphabets : ∀ k, Fintype ((machine F gamma rho).computer.Γ k) :=
  fun _ => inferInstanceAs (Fintype Bool)

def input (geometric : Bool) (m : ℕ) (y : Fin (m+1) → K) : Code (Fin 4) × List K :=
  (WeightCompiler.reference geometric m, List.ofFn y)

variable (base : D → Fin n → ℚ) (unit : D) (hunit : F.decode (base unit) = 1)
variable (hlit : ∀ a, ArithmeticSize.Bound (fun d => F.decode (base d)) 1
  (WeightFormulas.coefficients gamma rho a))

abbrev width (m Y : ℕ) := ArithmeticSize.bitBound F base (PB.budget m Y)

include unit hunit hlit in
/-- All literal, answer and intermediate value words obey this explicit bit bound. -/
theorem trace_width (geometric : Bool) (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i)) :
    ∀ x ∈ PB.trace gamma rho geometric m y,
      (F.encoding.encode x).length ≤ width F base m Y := by
  intro x hx
  exact (PB.trace_bound F base unit hunit gamma rho hlit geometric m Y y hy x hx).encoded_length_le F base

include unit hunit hlit in
/-- The certified trace is the actual reference run, including every stack boundary. -/
theorem certified (geometric : Bool) (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i)) :
    Certified F.encoding (RingFormulaMachine.coefficients F
      (fun a => F.decode.symm (WeightFormulas.coefficients gamma rho a)))
      (width F base m Y) (m+1+(WeightCompiler.reference geometric m).length)
      (WeightCompiler.reference geometric m) (List.ofFn y)
      [(resultPair gamma rho geometric m y).1,(resultPair gamma rho geometric m y).2]
      (PB.trace gamma rho geometric m y) := by
  have hc : RingFormulaMachine.coefficients F
      (fun a => F.decode.symm (WeightFormulas.coefficients gamma rho a)) =
      WeightFormulas.coefficients gamma rho := by
    funext a
    exact F.decode.apply_symm_apply _
  rw [hc]
  have hY : Y ≤ PB.budget m Y := by unfold PB.budget; nlinarith
  have hOne : 1 ≤ PB.budget m Y := by unfold PB.budget; nlinarith
  apply certified_of_run F.encoding (WeightFormulas.coefficients gamma rho)
    (width F base m Y) (m+1+(WeightCompiler.reference geometric m).length)
  · intro a
    exact ((hlit a).mono unit hunit hOne).encoded_length_le F base
  · exact (ArithmeticSize.Bound.zero unit (PB.budget m Y)).encoded_length_le F base
  · exact (ArithmeticSize.Bound.one.mono unit hunit (Nat.zero_le _)).encoded_length_le F base
  · exact PB.reference_run gamma rho geometric m y
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact ((hy i).mono unit hunit hY).encoded_length_le F base
  · exact trace_width F gamma rho base unit hunit hlit geometric m Y y hy
  · simp

include unit hunit hlit in
/-- The actual serialized final pair includes its two frames and terminator. -/
theorem result_length (geometric : Bool) (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i)) :
    ((DivisionStack.encoding F).encode (resultPair gamma rho geometric m y)).length ≤
      4*width F base m Y+5 := by
  have h := (certified F gamma rho base unit hunit hlit geometric m Y y hy).output_width
  have h₁ := h (resultPair gamma rho geometric m y).1 (by simp)
  have h₂ := h (resultPair gamma rho geometric m y).2 (by simp)
  rw [DivisionStack.encoding_length]
  omega

/-- Parsing, instruction execution and all operand transport are charged. -/
def interpreterTime (geometric : Bool) (m Y : ℕ) (y : Fin (m+1) → K) : ℕ :=
  2*(codeEncoding.encode (WeightCompiler.reference geometric m)).length +
    2*((stackEncoding F.encoding).encode (List.ofFn y)).length+6+
    (WeightCompiler.reference geometric m).length *
      Interpreter.instructionBound labelBound F.encoding (fieldProviders F)
        (width F base m Y) (m+1+(WeightCompiler.reference geometric m).length)

def timeBound (geometric : Bool) (m Y : ℕ) (y : Fin (m+1) → K) : ℕ :=
  interpreterTime F base geometric m Y y+8*width F base m Y+12+
    (DivisionStack.computes F).time.eval (4*width F base m Y+5)

/-- Clean execution of the real interpreter, with the original explicit time bound. -/
def interpreter_outputs (geometric : Bool) (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i)) :
    TM2OutputsInTime (interpreter F gamma rho).computer
      ((inputEncoding F).encode (input geometric m y))
      (some ((DivisionStack.encoding F).encode (resultPair gamma rho geometric m y)))
      (interpreterTime F base geometric m Y y) := by
  have h := PB.execute_reference F base unit hunit gamma rho hlit geometric m Y y hy
  exact {
    steps := h.choose
    evals_in_steps := h.choose_spec.2
    steps_le_m := h.choose_spec.1 }

/-- Actual composition executes one division after the certified ring-only run. -/
def outputs (geometric : Bool) (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i)) :
    TM2OutputsInTime (machine F gamma rho).computer
      ((inputEncoding F).encode (input geometric m y))
      (some (F.encoding.encode (result gamma rho geometric m y)))
      (timeBound F base geometric m Y y) := by
  let first := interpreter_outputs F gamma rho base unit hunit hlit geometric m Y y hy
  let last := (DivisionStack.computes F).outputs (resultPair gamma rho geometric m y)
  let all := BinaryCompose.Machine.compose_correct (interpreter F gamma rho)
    (DivisionStack.computes F).machine _ _ _ _ _ first last
  refine { steps := all.steps, evals_in_steps := all.evals_in_steps, steps_le_m := ?_ }
  have ht := all.steps_le_m
  have hs := result_length F gamma rho base unit hunit hlit geometric m Y y hy
  have hd := natPolynomial_eval_mono (DivisionStack.computes F).time hs
  unfold timeBound
  omega

/-- The same successful finite-machine execution returns I1's public value. -/
def outputs_evaluate (geometric : Bool) (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i))
    (hn : Function.Injective (nodes geometric rho m)) (hg : gamma ≠ 0) :
    TM2OutputsInTime (machine F gamma rho).computer
      ((inputEncoding F).encode (input geometric m y))
      (some (F.encoding.encode (Interpolation.evaluate (nodes geometric rho m)
        (normalized gamma m y)))) (timeBound F base geometric m Y y) := by
  rw [← result_eq_evaluate gamma rho geometric m y hn hg]
  exact outputs F gamma rho base unit hunit hlit geometric m Y y hy

end
end Postprocessor
end Counting.Algorithm.InterpolationMachine
