import Counting.Algorithm.InterpolationMachine.Compiler
import Holant.Proofs.Algorithms.TransformRecognition.RationalCompiler

/-!
# Concrete rational clients of the whole compiler/postprocessor machine

The scaled quadratic samples include two zero answers and a nonunit scaling.
The exact existing rational-field codec is reused, not replaced by integer output.
-/
namespace Counting.Algorithm.InterpolationMachine.Clients

open scoped BigOperators
open Turing Holant.Algebraic Holant.Complexity.BinaryInterpolation Holant.OneHot
open Holant.OneHot.StackProgram
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

abbrev rationalField := Holant.LocalDrafts.MainChain.TransformRecognition.RationalCompiler.field

def constants : Fin 5 → ℚ := ![2,2,-1,1,-16]
def base : Fin 5 → Fin 1 → ℚ := fun a => rationalField.decode.symm (constants a)

theorem base_decode (a : Fin 5) : rationalField.decode (base a) = constants a :=
  rationalField.decode.apply_symm_apply _

theorem unit_correct : rationalField.decode (base 3) = 1 := by rw [base_decode]; rfl

theorem literal_bound (a : Fin 4) :
    ArithmeticSize.Bound (fun d => rationalField.decode (base d)) 1
      (WeightFormulas.coefficients (2:ℚ) 2 a) := by
  have h := ArithmeticSize.Bound.coefficient (coeff:=fun d => rationalField.decode (base d)) a.castSucc
  rw [base_decode] at h
  fin_cases a <;> exact h

/-- Samples of `(X-1)*(X-3)`, multiplied by the nonunit scale `(2^(i+1))^2`. -/
def samples : Fin 3 → ℚ := ![0,-16,0]

/-- The two zero entries are genuine polynomial evaluations, after scaling. -/
theorem samples_scaled (i : Fin 3) : samples i =
    (scales (2:ℚ) 2 i)^2 * ((nodes false (2:ℚ) 2 i-1)*(nodes false (2:ℚ) 2 i-3)) := by
  fin_cases i <;> norm_num [samples, scales, nodes, WeightFormulas.scales, WeightFormulas.nodes]

theorem sample_bound (i : Fin 3) :
    ArithmeticSize.Bound (fun d => rationalField.decode (base d)) 1 (samples i) := by
  have hz := ArithmeticSize.Bound.zero (coeff:=fun d => rationalField.decode (base d)) (3:Fin 5) 1
  have hn := ArithmeticSize.Bound.coefficient (coeff:=fun d => rationalField.decode (base d)) (4:Fin 5)
  rw [base_decode] at hn
  fin_cases i
  · exact hz
  · exact hn
  · exact hz

/-- Both I1's executable evaluator and the generated ring program keep the zeros. -/
theorem quadratic_evaluate :
    Interpolation.evaluate (nodes false (2:ℚ) 2) (normalized 2 2 samples) = 1 := by
  rw [Interpolation.evaluate_eq_recoverTop]
  change (∑ i : Fin 3, normalized (2:ℚ) 2 samples i /
    ∏ j ∈ Finset.univ.erase i, (nodes false (2:ℚ) 2 i - nodes false (2:ℚ) 2 j)) = 1
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  norm_num [nodes, WeightFormulas.nodes, normalized, scales, WeightFormulas.scales, samples,
    hu, Finset.erase_insert, Finset.erase_insert_of_ne, Finset.erase_singleton]

theorem quadratic_result : result (2:ℚ) 2 false 2 samples = 1 := by
  rw [result_eq_evaluate (2:ℚ) 2 false 2 samples (arithmetic_nodes_injective 2 2) (by norm_num)]
  exact quadratic_evaluate

theorem quadratic_denominator : (resultPair (2:ℚ) 2 false 2 samples).2 ≠ 0 :=
  denominator_ne_zero 2 2 false 2 samples (arithmetic_nodes_injective 2 2) (by norm_num)

/-- A concrete clean TM2 execution, starting from unary 2 and the scaled samples. -/
def quadratic_machine :
    TM2OutputsInTime (Compiler.machine rationalField 2 2 false).computer
      ((Compiler.inputEncoding rationalField).encode (Compiler.input 2 samples))
      (some (rationalField.encoding.encode 1))
      (Compiler.timeBound rationalField false base 2 1 samples) := by
  rw [← quadratic_result]
  exact Compiler.outputs rationalField 2 2 false base 3 unit_correct literal_bound 2 1 samples sample_bound

/-- The whole machine also returns zero for arbitrarily many zero samples. -/
def zero_machine (m : ℕ) :
    TM2OutputsInTime (Compiler.machine rationalField 2 2 false).computer
      ((Compiler.inputEncoding rationalField).encode (Compiler.input m (fun _ => 0)))
      (some (rationalField.encoding.encode 0))
      (Compiler.timeBound rationalField false base m 1 (fun _ => 0)) := by
  have h := Compiler.outputs rationalField 2 2 false base 3 unit_correct literal_bound m 1
    (fun _ => 0) (fun _ => ArithmeticSize.Bound.zero (3:Fin 5) 1)
  simpa only [result_zero] using h

/-- The zero-answer run uses legal denominators at every degree. -/
theorem zero_denominator (m : ℕ) : (resultPair (2:ℚ) 2 false m (fun _ => 0)).2 ≠ 0 :=
  denominator_ne_zero 2 2 false m _ (arithmetic_nodes_injective 2 m) (by norm_num)

/-- Degree zero still generates code, evaluates its empty products and divides by one. -/
def degree_zero_machine :
    TM2OutputsInTime (Compiler.machine rationalField 2 2 true).computer
      ((Compiler.inputEncoding rationalField).encode (Compiler.input 0 (fun _ => -16)))
      (some (rationalField.encoding.encode (-16)))
      (Compiler.timeBound rationalField true base 0 1 (fun _ => -16)) := by
  have hb : ArithmeticSize.Bound (fun d => rationalField.decode (base d)) 1 (-16:ℚ) := by
    have h := ArithmeticSize.Bound.coefficient (coeff:=fun d => rationalField.decode (base d)) (4:Fin 5)
    have hc : rationalField.decode (base 4) = (-16:ℚ) := by rw [base_decode]; rfl
    rw [hc] at h
    exact h
  have h := Compiler.outputs rationalField 2 2 true base 3 unit_correct literal_bound 0 1
    (fun _ => -16) (fun _ => hb)
  simpa only [result_zero_degree] using h

/-- Executable syntax/interpreter client; its output pair has a nonzero denominator. -/
def runQuadratic : Option (List ℚ × List ℚ) :=
  run (WeightFormulas.coefficients 2 2) (WeightCompiler.reference false 2) [0,-16,0]

/-- Actual generated ring execution, including the ordered zero samples. -/
theorem runQuadratic_values : runQuadratic.map Prod.fst = some [-16384,-16384] := by
  change (run (WeightFormulas.coefficients (2:ℚ) 2) (WeightCompiler.reference false 2)
    (List.ofFn samples)).map Prod.fst = _
  rw [Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds.reference_run]
  have hu : (Finset.univ : Finset (Fin 3)) = {0,1,2} := by decide
  change (some ([∑ i : Fin 3, samples i * ∏ j ∈ Finset.univ.erase i,
    queryDenominator (WeightFormulas.nodes false (2:ℚ) 2) (WeightFormulas.scales 2 2) j,
    ∏ i : Fin 3, queryDenominator (WeightFormulas.nodes false (2:ℚ) 2)
      (WeightFormulas.scales 2 2) i] : List ℚ) : Option (List ℚ)) = some [-16384,-16384]
  norm_num [queryDenominator, interpolationDenominator, WeightFormulas.nodes, WeightFormulas.scales,
    samples, hu, Finset.erase_insert, Finset.erase_insert_of_ne, Finset.erase_singleton]

end
end Counting.Algorithm.InterpolationMachine.Clients
