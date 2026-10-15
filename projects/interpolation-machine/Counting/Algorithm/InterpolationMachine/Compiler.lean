import Counting.Algorithm.InterpolationMachine.Postprocessor
import Holant.Complexity.BinaryInterpolation.WeightCompiler.Bounds

/-!
# Physical code generation followed by exact-field recovery

The external input is a framed unary degree and a framed list of canonical field
answers. A real finite machine generates the weight bytecode, preserves the
answers, and invokes the actual postprocessor. No code generation is free.
-/
namespace Counting.Algorithm.InterpolationMachine.Compiler

open Turing Computability Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose Holant.Complexity.BinaryInterpolation
open Holant.Complexity.FixedFieldMachines
open Holant.OneHot Holant.OneHot.StackProgram
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
variable {K D : Type} [Field K] [Algebra ℚ K] [Fintype D] {n : ℕ}
variable (F : FixedField K n) (gamma rho : K) (geometric : Bool)

abbrev inputEncoding := pairEncoding WeightCompiler.unary (stackEncoding F.encoding)

/-- The compiler's actual machine input, before any bytecode has been generated. -/
def input (m : ℕ) (y : Fin (m+1) → K) : ℕ × List K := (m,List.ofFn y)

/-- Preserve the encoded answer list while physically compiling the unary degree. -/
def prepare : Computes (inputEncoding F) (Postprocessor.inputEncoding F)
    (fun z : ℕ × List K => (WeightCompiler.reference geometric z.1,z.2)) :=
  pairComputes
    ((Wiring.firstComputes WeightCompiler.unary (stackEncoding F.encoding)).andThen
      (WeightCompiler.computes geometric))
    (Wiring.secondComputes WeightCompiler.unary (stackEncoding F.encoding))

/-- A single finite TM2, fixed before the degree and answers arrive. -/
abbrev machine := (prepare F geometric).machine.compose (Postprocessor.machine F gamma rho)

@[instance_reducible] def finiteAlphabets : ∀ k, Fintype ((machine F gamma rho geometric).computer.Γ k) :=
  fun _ => inferInstanceAs (Fintype Bool)

variable (base : D → Fin n → ℚ) (unit : D) (hunit : F.decode (base unit) = 1)
variable (hlit : ∀ a, ArithmeticSize.Bound (fun d => F.decode (base d)) 1
  (WeightFormulas.coefficients gamma rho a))

/-- Charges the physical generator, transfer of both code and answers, and all
postprocessing. Intermediate bit bounds are in `Postprocessor.width`. -/
def timeBound (m Y : ℕ) (y : Fin (m+1) → K) : ℕ :=
  (prepare F geometric).time.eval ((inputEncoding F).encode (input m y)).length +
    2*(((Postprocessor.inputEncoding F).encode (Postprocessor.input geometric m y)).length+1)+
    Postprocessor.timeBound F base geometric m Y y

def outputs (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i)) :
    TM2OutputsInTime (machine F gamma rho geometric).computer
      ((inputEncoding F).encode (input m y))
      (some (F.encoding.encode (result gamma rho geometric m y)))
      (timeBound F geometric base m Y y) :=
  BinaryCompose.Machine.compose_correct (prepare F geometric).machine
    (Postprocessor.machine F gamma rho) _ _ _ _ _
    ((prepare F geometric).outputs (input m y))
    (Postprocessor.outputs F gamma rho base unit hunit hlit geometric m Y y hy)

/-- Exact transition count of the successful combined run, including transport. -/
@[simp] theorem outputs_steps (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i)) :
    (outputs F gamma rho geometric base unit hunit hlit m Y y hy).steps =
      (Postprocessor.outputs F gamma rho base unit hunit hlit geometric m Y y hy).steps +
        (2*(((Postprocessor.inputEncoding F).encode (Postprocessor.input geometric m y)).length+1)+
          ((prepare F geometric).outputs (input m y)).steps) := rfl

/-- The concrete front end and postprocessor return I1's actual list-fold value. -/
def outputs_evaluate (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i))
    (hn : Function.Injective (nodes geometric rho m)) (hg : gamma ≠ 0) :
    TM2OutputsInTime (machine F gamma rho geometric).computer
      ((inputEncoding F).encode (input m y))
      (some (F.encoding.encode (Interpolation.evaluate (nodes geometric rho m)
        (normalized gamma m y)))) (timeBound F geometric base m Y y) := by
  rw [← result_eq_evaluate gamma rho geometric m y hn hg]
  exact outputs F gamma rho geometric base unit hunit hlit m Y y hy

/-- On genuine scaled polynomial samples, the complete machine recovers the
highest coefficient at the supplied degree bound. -/
def outputs_coefficient (m Y : ℕ) (P : Polynomial K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y
      ((scales gamma m i)^m * P.eval (nodes geometric rho m i)))
    (hn : Function.Injective (nodes geometric rho m)) (hg : gamma ≠ 0)
    (hP : P.natDegree ≤ m) :
    TM2OutputsInTime (machine F gamma rho geometric).computer
      ((inputEncoding F).encode
        (input m (fun i => (scales gamma m i)^m * P.eval (nodes geometric rho m i))))
      (some (F.encoding.encode (P.coeff m)))
      (timeBound F geometric base m Y
        (fun i => (scales gamma m i)^m * P.eval (nodes geometric rho m i))) := by
  rw [← result_eq_coefficient gamma rho geometric m P hn hg hP]
  exact outputs F gamma rho geometric base unit hunit hlit m Y _ hy

end
end Counting.Algorithm.InterpolationMachine.Compiler
