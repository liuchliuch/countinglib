import Paper2.ExactInput.FixedRootCodec.ReverseCoefficient
import Paper2.Complexity.BellMachines.RationalArithmetic.ScalarMachines

/-! The common denominator is calculated from every literal sparse record.
The product may be numerically large, but its binary length grows at most
linearly in the sum of the input coefficient bit lengths. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines GraphPreprocessing
noncomputable section
set_option backward.isDefEq.respectTransparency false

def sparseDenominator (p : RationalPolynomialCode) : ℕ := (p.map (fun t => t.2.den)).prod

theorem sparseDenominator_pos (p : RationalPolynomialCode) : 0<sparseDenominator p := by
  induction p with
  | nil => simp [sparseDenominator]
  | cons t p ih => simpa [sparseDenominator] using Nat.mul_pos t.2.den_pos ih

abbrev DenominatorState := RationalPolynomialCode × (ℕ × ℕ)
abbrev denominatorStateEncoding := pairEncoding polynomialEncoding
  (pairEncoding UnaryBinary.unaryEncoding encodingNatBool)

def denominatorStep (s : DenominatorState) : DenominatorState :=
  (s.1,s.2.1+1,s.2.2*(s.1.getD s.2.1 (0,0)).2.den)

def denominatorStepComputes :
    Computes denominatorStateEncoding denominatorStateEncoding denominatorStep := by
  let p := Wiring.firstComputes polynomialEncoding (pairEncoding UnaryBinary.unaryEncoding encodingNatBool)
  let tail := Wiring.secondComputes polynomialEncoding (pairEncoding UnaryBinary.unaryEncoding encodingNatBool)
  let index := tail.andThen (Wiring.firstComputes UnaryBinary.unaryEncoding encodingNatBool)
  let acc := tail.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding encodingNatBool)
  let term := (pairComputes p index).andThen (listGetDComputes sparseTermEncoding (0,0))
  let den := (term.andThen (Wiring.secondComputes encodingNatBool rationalEncoding)).andThen
    RationalArithmetic.denominatorComputes
  let product := (pairComputes acc den).andThen RationalArithmetic.naturalMultiplicationComputes
  exact congrComputes (pairComputes p
    (pairComputes (index.andThen unarySuccessorComputes) product)) (fun _ => rfl)

theorem denominator_polynomial_iterate (s : DenominatorState) (k : ℕ) :
    ((denominatorStep^[k]) s).1=s.1 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Function.iterate_succ_apply',denominatorStep] using ih

theorem denominator_index_iterate (s : DenominatorState) (k : ℕ) :
    ((denominatorStep^[k]) s).2.1=s.2.1+k := by
  induction k with
  | zero => simp
  | succ k ih => simpa only [Function.iterate_succ_apply',denominatorStep,ih,Nat.add_assoc]

theorem sparse_getD_denominator_bits (p : RationalPolynomialCode) (i : ℕ) :
    (p.getD i (0,0)).2.den.size≤(polynomialEncoding.encode p).length+1 := by
  by_cases hi : i<p.length
  · rw [List.getD_eq_getElem p (0,0) hi]
    exact (Nat.size_le_size (le_max_right (p[i]).2.num.natAbs (p[i]).2.den)).trans
      ((rational_height_input _).trans
        (Nat.add_le_add_right (sparse_member_bits p _ (List.getElem_mem hi)) 1))
  · rw [List.getD_eq_default p (0,0) (by omega)]
    simp

theorem denominator_acc_bits (s : DenominatorState) (k : ℕ) :
    (((denominatorStep^[k]) s).2.2).size≤
      s.2.2.size+k*((polynomialEncoding.encode s.1).length+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change Nat.size (_*_)≤_
    have ha := natSize_mul_le (((denominatorStep^[k]) s).2.2)
      ((((denominatorStep^[k]) s).1).getD (((denominatorStep^[k]) s).2.1) (0,0)).2.den
    have hb := sparse_getD_denominator_bits (((denominatorStep^[k]) s).1)
      (((denominatorStep^[k]) s).2.1)
    rw [denominator_polynomial_iterate] at ha hb ⊢
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem denominatorStateEncoding_length (s : DenominatorState) :
    (denominatorStateEncoding.encode s).length=
      2*(polynomialEncoding.encode s.1).length+2*s.2.1+s.2.2.size+2 := by
  simp only [denominatorStateEncoding,pairEncoding_length,UnaryBinary.unaryEncoding,
    List.length_replicate,encodingNatBool,encodeNat_length]
  omega

theorem denominator_intermediate :
    BoundedIterate.IntermediateBound denominatorStateEncoding denominatorStep coefficientSpace := by
  intro n s k hk
  let N := ((BoundedIterate.inputEncoding denominatorStateEncoding).encode (n,s)).length
  have hn : N=2*n+1+(denominatorStateEncoding.encode s).length := by
    simp [N,BoundedIterate.inputEncoding,pairEncoding,UnaryBinary.unaryEncoding]
  have hs := denominatorStateEncoding_length s
  have hp : (polynomialEncoding.encode s.1).length≤N := by omega
  have hi : s.2.1≤N := by omega
  have ha : s.2.2.size≤N := by omega
  have hkN : k≤N := by omega
  have hb := denominator_acc_bits s k
  have hm : k*((polynomialEncoding.encode s.1).length+1)≤N*(N+1) :=
    Nat.mul_le_mul hkN (by omega)
  have hl := denominatorStateEncoding_length ((denominatorStep^[k]) s)
  rw [denominator_polynomial_iterate,denominator_index_iterate] at hl
  change _≤coefficientSpace.eval N
  simp only [coefficientSpace,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_pow,Polynomial.eval_X]
  nlinarith

theorem sparseDenominator_drop (p : RationalPolynomialCode) (i : ℕ) :
    sparseDenominator (p.drop i)=(p.getD i (0,0)).2.den*
      sparseDenominator (p.drop (i+1)) := by
  induction p generalizing i with
  | nil => simp [sparseDenominator]
  | cons t p ih =>
    cases i with
    | zero => simp [sparseDenominator]
    | succ i => simpa using ih i

theorem denominator_invariant (s : DenominatorState) (k : ℕ) :
    ((denominatorStep^[k]) s).2.2*
      sparseDenominator ((((denominatorStep^[k]) s).1).drop
        (((denominatorStep^[k]) s).2.1))=
      s.2.2*sparseDenominator (s.1.drop s.2.1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change ((denominatorStep^[k]) s).2.2*
      ((((denominatorStep^[k]) s).1).getD (((denominatorStep^[k]) s).2.1) (0,0)).2.den*
      sparseDenominator ((((denominatorStep^[k]) s).1).drop
        (((denominatorStep^[k]) s).2.1+1))= _
    rw [mul_assoc,← sparseDenominator_drop]
    exact ih

/-- Actual finite bit program for a common denominator of arbitrary sparse
coefficients. No numerical magnitude is used as a loop counter. -/
def sparseDenominatorComputes :
    Computes polynomialEncoding encodingNatBool sparseDenominator := by
  let start : Computes polynomialEncoding denominatorStateEncoding (fun p => (p,0,1)) :=
    pairComputes (identityComputes polynomialEncoding)
      (pairComputes (constantComputes polynomialEncoding UnaryBinary.unaryEncoding 0)
        (constantComputes polynomialEncoding encodingNatBool 1))
  let rounds := Lists.lengthUnaryComputes sparseTermEncoding
  let loop := BoundedIterate.computes denominatorStateEncoding denominatorStep
    denominatorStepComputes coefficientSpace denominator_intermediate
  let extract := (Wiring.secondComputes polynomialEncoding
    (pairEncoding UnaryBinary.unaryEncoding encodingNatBool)).andThen
      (Wiring.secondComputes UnaryBinary.unaryEncoding encodingNatBool)
  apply congrComputes (((pairComputes rounds start).andThen loop).andThen extract)
  intro p
  have h := denominator_invariant (p,0,1) p.length
  rw [denominator_polynomial_iterate,denominator_index_iterate] at h
  simpa only [Function.comp_apply,List.drop_length,List.drop_zero,Nat.zero_add,
    sparseDenominator,List.map_nil,List.prod_nil,mul_one,one_mul] using h

end
end Paper2.ExactInput.FixedRootCodec
