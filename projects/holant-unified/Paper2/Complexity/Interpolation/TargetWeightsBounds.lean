import Paper2.Complexity.Interpolation.TargetWeights

/-! Explicit size and intermediate-value bounds for target interpolation.
Answers carry the same fixed-family certificates as the physical oracle
networks; their possibly cancelled output words do not stand in for graph size. -/
namespace Paper2.Complexity.Interpolation.TargetWeights
open Computability Holant.Algebraic
open Holant.Complexity Holant.Complexity.BinaryCompose
open Holant.Complexity.FixedFieldMachines
open Holant.Complexity.BinaryInterpolation
open Holant.OneHot Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
open RingFormula WeightCompiler
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

def numeratorSize (m : ℕ) : ℕ := (m+1)*(2*m+8)+1
def weightSize (m : ℕ) : ℕ := numeratorSize m + WeightFormulas.weightSize m + 1
def codeBound (m : ℕ) : ℕ := (m+2)*weightSize m+4*(m+1)+2

theorem targetFactor_size (j : ℕ) : (targetFactor j).size = 2*j+7 := by
  simp [targetFactor,size,WeightFormulas.node_size]
  omega

theorem targetNumerator_size_le (m : ℕ) (i : Fin (m+1)) :
    (targetNumerator m i).size ≤ numeratorSize m := by
  apply size_without_le
  · omega
  · intro j
    rw [targetFactor_size]
    have hj := j.isLt
    omega

theorem weight_size_le (m : ℕ) (i : Fin (m+1)) : (weight m i).size ≤ weightSize m := by
  have hn := targetNumerator_size_le m i
  have hw := WeightFormulas.weight_size_le false m i
  simp only [weight,size,weightSize]
  omega

theorem totalDenominator_size_le (m : ℕ) :
    (WeightFormulas.totalDenominator false m).size ≤ weightSize m := by
  have h := WeightFormulas.totalDenominator_size_le false m
  unfold weightSize
  omega

theorem reference_length_le (m : ℕ) : (reference m).length ≤ codeBound m := by
  have hw : ((List.ofFn (weight m)).flatMap
      (fun p => p.code ++ ([.copy 2,.mul,.add,.erase 1] : WeightCompiler.Code))).length ≤
      (m+1)*(weightSize m+4) := by
    rw [List.length_flatMap,List.map_ofFn,Fin.sum_ofFn]
    calc
      _ ≤ ∑ _i : Fin (m+1), (weightSize m+4) := by
        apply Finset.sum_le_sum
        intro i _
        simpa [RingFormula.code_length] using Nat.add_le_add_right (weight_size_le m i) 4
      _ = _ := by simp
  have hd := totalDenominator_size_le m
  simp only [reference,weighted_code,List.length_append,List.length_singleton,RingFormula.code_length]
  unfold codeBound
  nlinarith

def codePolynomial : Polynomial ℕ :=
  let X := Polynomial.X
  let D := 2*((X+1)*X)+(X+1)*(4*X+10)+3
  let W := (X+1)*(D+1)+1
  let T := (X+1)*(2*X+8)+1+W+1
  (X+2)*T+4*(X+1)+2

theorem codePolynomial_eval (m : ℕ) : codePolynomial.eval m = codeBound m := by
  simp [codePolynomial,codeBound,weightSize,numeratorSize,
    WeightFormulas.weightSize,WeightFormulas.denominatorSize]

theorem weight_le_codePolynomial (m : ℕ) : weightSize m ≤ codePolynomial.eval m := by
  rw [codePolynomial_eval]
  unfold codeBound
  nlinarith

def budget (m Y : ℕ) : ℕ := (m+1)*(Y+weightSize m+1)

variable {K D : Type} [Field K] [Algebra ℚ K] [Fintype D] {n : ℕ}
variable (F : FixedField K n) (base : D → Fin n → ℚ)
variable (unit : D) (hunit : F.decode (base unit) = 1) (gamma z : K)

include unit hunit in
theorem trace_bound
    (hlit : ∀ a, ArithmeticSize.Bound (fun d => F.decode (base d)) 1
      (WeightFormulas.coefficients gamma z a))
    (m Y : ℕ) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) Y (y i)) :
    ∀ x ∈ trace gamma z m y,
      ArithmeticSize.Bound (fun d => F.decode (base d)) (budget m Y) x := by
  have hw := Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds.weighted_bound
    (WeightFormulas.coefficients gamma z) (fun d => F.decode (base d)) unit hunit hlit
    (List.ofFn (fun i => (weight m i,y i))) Y (weightSize m) 0 0
    (by intro p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp; exact weight_size_le m i)
    (by intro p hp; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp; exact hy i)
    (ArithmeticSize.Bound.zero unit 0)
  have hd := Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds.formula_bound
    (WeightFormulas.coefficients gamma z) (fun d => F.decode (base d)) unit hunit hlit
    (WeightFormulas.totalDenominator false m)
  have hsize : (WeightFormulas.totalDenominator false m).size ≤ budget m Y := by
    have h := totalDenominator_size_le m
    unfold budget
    nlinarith
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · simpa [budget] using hw.2 x hx
  · exact (hd.2 x hx).mono unit hunit hsize

/-- A single polynomial controls the entire stack trace and height from the
retained context length. -/
def structuralPolynomial (Y : Polynomial ℕ) : Polynomial ℕ :=
  (Polynomial.X+2)*(Y+codePolynomial+1)+codePolynomial+Polynomial.X+1

theorem structural_bounds (Y : Polynomial ℕ) (m N : ℕ) (hm : m ≤ N) :
    let Q := (structuralPolynomial Y).eval N
    1 ≤ Q ∧ Y.eval N ≤ Q ∧ budget m (Y.eval N) ≤ Q ∧
      m+1+(reference m).length ≤ Q := by
  dsimp only
  have hw := (weight_le_codePolynomial m).trans (natPolynomial_eval_mono codePolynomial hm)
  have hc : (reference m).length ≤ codePolynomial.eval N := by
    calc
      _ ≤ codeBound m := reference_length_le m
      _ = codePolynomial.eval m := (codePolynomial_eval m).symm
      _ ≤ codePolynomial.eval N := natPolynomial_eval_mono codePolynomial hm
  simp only [structuralPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_ofNat,budget]
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor
  · have hh := Nat.mul_le_mul (Nat.add_le_add_right hm 1)
      (Nat.add_le_add_right (Nat.add_le_add_left hw (Y.eval N)) 1)
    nlinarith
  · nlinarith

def literalCoordinates : Fin 4 → Fin n → ℚ :=
  fun a => F.decode.symm (WeightFormulas.coefficients gamma z a)

def interpreter := StackInputInterpreter.machine
  (Kernels.machine (RingFormulaMachine.literals F (literalCoordinates F gamma z)) (fieldProviders F))
  WeightCompiler.labels (RingFormulaMachine.labelBound WeightCompiler.labels)

include unit hunit in
theorem certified
    (hlit : ∀ a, ArithmeticSize.Bound (fun d => F.decode (base d)) 1
      (WeightFormulas.coefficients gamma z a))
    (Y : Polynomial ℕ) (m N : ℕ) (hm : m ≤ N) (y : Fin (m+1) → K)
    (hy : ∀ i, ArithmeticSize.Bound (fun d => F.decode (base d)) (Y.eval N) (y i)) :
    Certified F.encoding (RingFormulaMachine.coefficients F (literalCoordinates F gamma z))
      (ArithmeticSize.bitBound F base ((structuralPolynomial Y).eval N))
      ((structuralPolynomial Y).eval N) (reference m) (List.ofFn y)
      [(resultPair gamma z m y).1,(resultPair gamma z m y).2] (trace gamma z m y) := by
  let Q := (structuralPolynomial Y).eval N
  have hq := structural_bounds Y m N hm
  have hcoeff : RingFormulaMachine.coefficients F (literalCoordinates F gamma z) =
      WeightFormulas.coefficients gamma z := by
    funext a
    exact F.decode.apply_symm_apply _
  rw [hcoeff]
  apply certified_of_run F.encoding (WeightFormulas.coefficients gamma z)
    (ArithmeticSize.bitBound F base Q) Q
  · intro a
    exact ((hlit a).mono unit hunit hq.1).encoded_length_le F base
  · exact (ArithmeticSize.Bound.zero unit Q).encoded_length_le F base
  · exact (ArithmeticSize.Bound.one.mono unit hunit (Nat.zero_le Q)).encoded_length_le F base
  · exact reference_run gamma z m y
  · intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact ((hy i).mono unit hunit hq.2.1).encoded_length_le F base
  · intro x hx
    exact ((trace_bound F base unit hunit gamma z hlit m (Y.eval N) y hy x hx).mono
      unit hunit hq.2.2.1).encoded_length_le F base
  · simpa using hq.2.2.2

end
end Paper2.Complexity.Interpolation.TargetWeights
