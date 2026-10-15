import Holant.Complexity.BinaryInterpolation.WeightCompiler.Bounds
import Holant.Proofs.BinaryInterpolation.PostprocessBounds
import Holant.Complexity.BinaryInterpolation.DivisionStack

/-! Target-value interpolation at the fixed positive integer nodes.  The
target and scalar are literal field constants; the degree is a unary runtime
input.  All instruction words are emitted by the retained finite contextual
traversal machines. -/
namespace Paper2.Complexity.Interpolation.TargetWeights
open Computability Holant.Algebraic
open Holant.Complexity Holant.Complexity.BinaryCompose
open Holant.Complexity.FixedFieldMachines Holant.Complexity.GraphPreprocessing
open Holant.Complexity.GraphPreprocessing.OriginalCoefficient
open Holant.Complexity.FixedGadgetSubstitution.Compiler
open Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Holant.Complexity.BinaryInterpolation
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open RingFormula WeightCompiler
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096

abbrev Formula := RingFormula (Fin 4)

def targetFactor (j : ℕ) : Formula :=
  .add (.literal 1) (.mul (.literal 2) (WeightFormulas.node false (j+1)))

def targetNumerator (m : ℕ) (i : Fin (m+1)) : Formula :=
  without (fun j : Fin (m+1) => targetFactor j.val) i

def weight (m : ℕ) (i : Fin (m+1)) : Formula :=
  .mul (targetNumerator m i) (WeightFormulas.weight false m i)

def reference (m : ℕ) : WeightCompiler.Code :=
  [.zero] ++ WeightedStack.code (List.ofFn (weight m)) ++
    (WeightFormulas.totalDenominator false m).code ++ [.swap]

def targetFactorCode (j : ℕ) : WeightCompiler.Code :=
  WeightCompiler.nodeCode false (j+1) ++ [.literal 2,.mul,.literal 1,.add]

def targetNumeratorCode (m i : ℕ) : WeightCompiler.Code :=
  [.one] ++ (List.range (m+1)).reverse.flatMap
    (fun j => (if j=i then [.one] else targetFactorCode j) ++ [.mul])

def weightCode (m i : ℕ) : WeightCompiler.Code :=
  WeightCompiler.weightCode false m i ++ targetNumeratorCode m i ++ [.mul]

def generatedCode (m : ℕ) : WeightCompiler.Code :=
  [.zero] ++ (List.range (m+1)).flatMap
    (fun i => weightCode m i ++ [.copy 2,.mul,.add,.erase 1]) ++
      totalDenominatorCode false m ++ [.swap]

theorem targetFactor_code (j : ℕ) : (targetFactor j).code = targetFactorCode j := by
  simp [targetFactor,targetFactorCode,code,node_code,List.append_assoc]

theorem targetNumerator_code (m : ℕ) (i : Fin (m+1)) :
    (targetNumerator m i).code = targetNumeratorCode m i.val := by
  simp only [targetNumerator,without,prodList_code]
  rw [ofFn_code_flatMap (f := fun j =>
    if j=i.val then [.one] else targetFactorCode j)]
  · rfl
  · intro j
    by_cases h : j=i
    · subst j; simp [code]
    · have hv : j.val ≠ i.val := fun e => h (Fin.ext e)
      simp [h,hv,targetFactor_code]

theorem weight_code (m : ℕ) (i : Fin (m+1)) :
    (weight m i).code = weightCode m i.val := by
  simp [weight,weightCode,code,WeightCompiler.weight_code,targetNumerator_code]

theorem generated_eq_reference (m : ℕ) : generatedCode m = reference m := by
  simp only [reference,weighted_code,totalDenominator_code,List.ofFn_eq_map,
    List.flatMap_map,Function.comp_def,weight_code]
  unfold generatedCode
  rw [←List.map_coe_finRange_eq_range]
  simp only [List.flatMap_map]

def targetFactorEmits : Emits unary targetFactorCode :=
  appendEmits ((successorComputes.andThen (nodeEmits false)))
    (constantEmits unary [.literal 2,.mul,.literal 1,.add])

def targetFactorAtEmits : Emits tripleUnary
    (fun x => (if x.2=x.1.2 then [.one] else targetFactorCode x.2) ++ [.mul]) := by
  let chosen := ifEmits equalIndicesComputes (constantEmits tripleUnary [.one])
    (thirdUnary.andThen targetFactorEmits)
  exact congrComputes (appendEmits chosen (constantEmits tripleUnary [.mul]))
    (fun x => by simp)

def targetNumeratorEmits : Emits pairUnary
    (fun x => targetNumeratorCode x.1 x.2) :=
  appendEmits (constantEmits pairUnary [.one])
    (reverseRangeEmits pairUnary (fun x => x.1+1)
      (firstUnary.andThen successorComputes) _ targetFactorAtEmits)

def weightEmits : Emits pairUnary (fun x => weightCode x.1 x.2) :=
  appendEmits (appendEmits (WeightCompiler.weightEmits false) targetNumeratorEmits)
    (constantEmits pairUnary [.mul])

def generatedEmits : Emits unary generatedCode :=
  appendEmits (appendEmits (appendEmits (constantEmits unary [.zero])
    (rangeEmits unary (fun m => m+1) successorComputes _
      (appendEmits weightEmits (constantEmits pairUnary [.copy 2,.mul,.add,.erase 1]))))
    (totalDenominatorEmits false)) (constantEmits unary [.swap])

/-- One actual finite Boolean TM emits the target-evaluation program. -/
def compiler : Computes unary (codeEncoding labels) reference :=
  recode (joinComputes generatedEmits
    (constantComputes unary Frame.wordEncoding [false])) id (fun _ => rfl)
    (fun m => by
      change chunk (generatedCode m) ++ [false] =
        framedListEncode (opEncoding labels) (reference m)
      rw [generated_eq_reference]
      simpa only [chunk,List.append_nil,framedListEncode] using
        entries_append_encode (opEncoding labels) (reference m) [])

variable {K : Type*} [Field K]

def numerator (z : K) (m : ℕ) (i : Fin (m+1)) : K :=
  ∏ j ∈ Finset.univ.erase i, (z - ((j.val+1 : ℕ) : K))

def denominators (gamma : K) (m : ℕ) : Fin (m+1) → K :=
  queryDenominator (WeightFormulas.nodes false (0 : K) m) (WeightFormulas.scales gamma m)

def resultPair (gamma z : K) (m : ℕ) (y : Fin (m+1) → K) : K × K :=
  (commonNumerator (denominators gamma m) (fun i => y i * numerator z m i),
   commonDenominator (denominators gamma m))

def value (gamma z : K) (m : ℕ) (y : Fin (m+1) → K) : K :=
  (resultPair gamma z m y).1 / (resultPair gamma z m y).2

theorem targetFactor_eval (gamma z : K) (j : ℕ) :
    (targetFactor j).eval (WeightFormulas.coefficients gamma z) =
      z - ((j+1 : ℕ) : K) := by
  simp only [targetFactor,eval,WeightFormulas.eval_node]
  simp [WeightFormulas.coefficients,sub_eq_add_neg]

theorem targetNumerator_eval (gamma z : K) (m : ℕ) (i : Fin (m+1)) :
    (targetNumerator m i).eval (WeightFormulas.coefficients gamma z) = numerator z m i := by
  simp [targetNumerator,numerator,targetFactor_eval]

theorem weight_eval (gamma z : K) (m : ℕ) (i : Fin (m+1)) :
    (weight m i).eval (WeightFormulas.coefficients gamma z) =
      numerator z m i * ∏j∈Finset.univ.erase i, denominators gamma m j := by
  simp only [weight,eval,targetNumerator_eval,WeightFormulas.eval_weight]
  rfl

def trace (gamma z : K) (m : ℕ) (y : Fin (m+1) → K) : List K :=
  WeightedStack.trace (WeightFormulas.coefficients gamma z)
    (List.ofFn (fun i => (weight m i,y i))) 0 ++
    (WeightFormulas.totalDenominator false m).trace (WeightFormulas.coefficients gamma z)

theorem reference_run (gamma z : K) (m : ℕ) (y : Fin (m+1) → K) :
    run (WeightFormulas.coefficients gamma z) (reference m) (List.ofFn y) =
      some ([(resultPair gamma z m y).1,(resultPair gamma z m y).2],trace gamma z m y) := by
  have hw := WeightedStack.run_code (WeightFormulas.coefficients gamma z)
    (List.ofFn (fun i => (weight m i,y i))) 0 []
  simp only [List.map_ofFn,Function.comp_def,List.append_nil] at hw
  have hv : WeightedStack.value (WeightFormulas.coefficients gamma z)
      (List.ofFn (fun i => (weight m i,y i))) 0 = (resultPair gamma z m y).1 := by
    rw [WeightedStack.value_eq_sum]
    simp only [zero_add,List.map_ofFn,Function.comp_apply,Fin.sum_ofFn,weight_eval,
      resultPair,commonNumerator,mul_assoc]
  rw [hv] at hw
  simp only [reference,run_append]
  simp only [run,step,bind,Option.bind_some,pure,List.nil_append]
  simp only [hw,Option.bind_some,RingFormula.run_code,WeightFormulas.eval_totalDenominator]
  simp [run,step,trace,resultPair,denominators,List.append_assoc]
  rfl

variable [CharZero K]

theorem nodes_injective (m : ℕ) :
    Function.Injective (WeightFormulas.nodes false (0 : K) m) := by
  intro i j h
  simp only [WeightFormulas.nodes,Bool.false_eq_true,↓reduceIte] at h
  exact Fin.ext (by exact Nat.add_right_cancel (Nat.cast_injective h))

theorem denominator_nonzero (gamma : K) (hgamma : gamma ≠ 0) (m : ℕ)
    (i : Fin (m+1)) : denominators gamma m i ≠ 0 :=
  queryDenominator_ne_zero _ _ (nodes_injective m)
    (fun j => pow_ne_zero _ hgamma) i

/-- Exact normalized target-value Lagrange sum, with every answer retained. -/
theorem value_eq_sum (gamma z : K) (hgamma : gamma ≠ 0) (m : ℕ)
    (y : Fin (m+1) → K) : value gamma z m y =
      ∑i, y i * numerator z m i /
        (gamma ^ ((i.val+1)*m) * interpolationDenominator
          (fun j : Fin (m+1) => ((j.val+1 : ℕ) : K)) i) := by
  rw [value,resultPair,←sum_div_common _ _ (denominator_nonzero gamma hgamma m)]
  simp only [denominators,queryDenominator,WeightFormulas.scales,pow_mul]
  rfl

end
end Paper2.Complexity.Interpolation.TargetWeights
