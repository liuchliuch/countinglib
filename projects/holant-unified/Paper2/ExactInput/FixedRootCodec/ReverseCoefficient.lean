import Paper2.ExactInput.FixedRootCodec.Combinators
import Paper2.ExactInput.FixedRootCodec.InputHeight
import Paper2.ExactInput.RootOutputSize
import Paper2.Complexity.BellMachines.UnaryList
import Paper2.Complexity.BellMachines.BoundedIterateInterface
import Paper2.Complexity.BellMachines.FieldArithmetic

/-! Literal sparse-polynomial coefficient extraction. Every input record is
visited by a polynomial-time stack controller, including repeated exponents,
zero coefficients, and records in arbitrary order. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler GraphPreprocessing.OriginalCoefficient
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev sparseTermEncoding := pairEncoding encodingNatBool rationalEncoding

def unarySuccessorComputes : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding
    Nat.succ :=
  recode (joinComputes (constantComputes UnaryBinary.unaryEncoding Frame.wordEncoding [true])
    (encodeComputes UnaryBinary.unaryEncoding)) id (fun _ => rfl)
    (fun n => by simp [UnaryBinary.unaryEncoding,List.replicate_succ,Frame.wordEncoding])

/-- Runtime unary indexing pads a physical list before selecting a proved valid
slot. The padding and the index itself are charged to the input word. -/
def listGetDComputes {A : Type} (e : Encoding A Bool) (default : A) :
    Computes (pairEncoding (framedListEncoding e) UnaryBinary.unaryEncoding) e
      (fun x => x.1.getD x.2 default) := by
  let xs := Wiring.firstComputes (framedListEncoding e) UnaryBinary.unaryEncoding
  let index := Wiring.secondComputes (framedListEncoding e) UnaryBinary.unaryEncoding
  let pad := (index.andThen unarySuccessorComputes).andThen (UnaryList.replicateComputes e default)
  let padded := (pairComputes xs pad).andThen (Lists.appendListsComputes e)
  let prepare : Computes (pairEncoding (framedListEncoding e) UnaryBinary.unaryEncoding)
      (ParentRowSelect.inputEncoding e)
      (fun x => ⟨x.1 ++ List.replicate (x.2+1) default,paddedIndex x.1 x.2 default⟩) :=
    recode (pairComputes padded index) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (prepare.andThen (ParentRowSelect.computes e))
    (fun x => padded_get x.1 x.2 default)

def selectedCoefficient (j : ℕ) (t : ℕ × ℚ) : ℚ := if t.1=j then t.2 else 0

def selectedCoefficientComputes (j : ℕ) :
    Computes sparseTermEncoding rationalEncoding (selectedCoefficient j) := by
  let exponent := Wiring.firstComputes encodingNatBool rationalEncoding
  let test := (pairComputes exponent
    (constantComputes sparseTermEncoding encodingNatBool j)).andThen (equalComputes encodingNatBool)
  exact congrComputes (ifComputes test (Wiring.secondComputes encodingNatBool rationalEncoding)
    (constantComputes sparseTermEncoding rationalEncoding 0)) (fun _ => by simp [selectedCoefficient])

abbrev CoefficientState := RationalPolynomialCode × (ℕ × ℚ)
abbrev coefficientStateEncoding := pairEncoding polynomialEncoding
  (pairEncoding UnaryBinary.unaryEncoding rationalEncoding)

def coefficientStep (j : ℕ) (s : CoefficientState) : CoefficientState :=
  (s.1,s.2.1+1,s.2.2+selectedCoefficient j (s.1.getD s.2.1 (0,0)))

def coefficientStepComputes (j : ℕ) :
    Computes coefficientStateEncoding coefficientStateEncoding (coefficientStep j) := by
  let p := Wiring.firstComputes polynomialEncoding (pairEncoding UnaryBinary.unaryEncoding rationalEncoding)
  let tail := Wiring.secondComputes polynomialEncoding (pairEncoding UnaryBinary.unaryEncoding rationalEncoding)
  let index := tail.andThen (Wiring.firstComputes UnaryBinary.unaryEncoding rationalEncoding)
  let acc := tail.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding rationalEncoding)
  let term := (pairComputes p index).andThen (listGetDComputes sparseTermEncoding (0,0))
  let selected := term.andThen (selectedCoefficientComputes j)
  exact congrComputes (pairComputes p
    (pairComputes (index.andThen unarySuccessorComputes) (rationalProvider.addComputes acc selected)))
    (fun _ => rfl)

theorem coefficient_polynomial_iterate (j : ℕ) (s : CoefficientState) (k : ℕ) :
    (((coefficientStep j)^[k]) s).1=s.1 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Function.iterate_succ_apply',coefficientStep] using ih

theorem coefficient_index_iterate (j : ℕ) (s : CoefficientState) (k : ℕ) :
    (((coefficientStep j)^[k]) s).2.1=s.2.1+k := by
  induction k with
  | zero => simp
  | succ k ih => simpa only [Function.iterate_succ_apply',coefficientStep,ih,Nat.add_assoc]

theorem sparse_member_bits (p : RationalPolynomialCode) (t : ℕ × ℚ) (ht : t∈p) :
    (rationalEncoding.encode t.2).length ≤ (polynomialEncoding.encode p).length := by
  induction p with
  | nil => simp at ht
  | cons u p ih =>
    have hp : (polynomialEncoding.encode (u::p)).length =
        2*(sparseTermEncoding.encode u).length+2+(polynomialEncoding.encode p).length := by
      simp [polynomialEncoding,framedListEncoding,framedListEncode,framedProductEncoding,
        sparseTermEncoding,pairEncoding,frame_length]
      omega
    have hu : (rationalEncoding.encode u.2).length ≤ (sparseTermEncoding.encode u).length := by
      simp only [sparseTermEncoding,pairEncoding_length]
      omega
    rcases List.mem_cons.mp ht with he | ht
    · subst t; omega
    · have h := ih ht; omega

theorem sparse_getD_height (p : RationalPolynomialCode) (i j : ℕ) :
    rationalBitHeight (selectedCoefficient j (p.getD i (0,0))) ≤
      (polynomialEncoding.encode p).length+1 := by
  by_cases hi : i<p.length
  · rw [List.getD_eq_getElem p (0,0) hi]
    by_cases hj : (p[i]).1=j
    · simp only [selectedCoefficient,hj,ite_true]
      exact (rational_height_input _).trans
        (Nat.add_le_add_right (sparse_member_bits p _ (List.getElem_mem hi)) 1)
    · simp [selectedCoefficient,hj,rationalBitHeight,rationalHeight]
  · rw [List.getD_eq_default p (0,0) (by omega)]
    simp [selectedCoefficient,rationalBitHeight,rationalHeight]

theorem coefficient_acc_height (j : ℕ) (s : CoefficientState) (k : ℕ) :
    rationalBitHeight (((coefficientStep j)^[k] s).2.2) ≤
      rationalBitHeight s.2.2+k*((polynomialEncoding.encode s.1).length+3) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change rationalBitHeight (_+_)≤_
    have ha := rationalBitHeight_add (((coefficientStep j)^[k] s).2.2)
      (selectedCoefficient j ((((coefficientStep j)^[k] s).1).getD
        (((coefficientStep j)^[k] s).2.1) (0,0)))
    have hb := sparse_getD_height (((coefficientStep j)^[k] s).1)
      (((coefficientStep j)^[k] s).2.1) j
    rw [coefficient_polynomial_iterate] at ha hb
    rw [coefficient_polynomial_iterate]
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem coefficientStateEncoding_length (s : CoefficientState) :
    (coefficientStateEncoding.encode s).length=
      2*(polynomialEncoding.encode s.1).length+2*s.2.1+
      (rationalEncoding.encode s.2.2).length+2 := by
  simp only [coefficientStateEncoding,pairEncoding_length,UnaryBinary.unaryEncoding,List.length_replicate]
  omega

def coefficientSpace : Polynomial ℕ := 3*Polynomial.X^2+20*Polynomial.X+20

theorem coefficient_intermediate (j : ℕ) :
    BoundedIterate.IntermediateBound coefficientStateEncoding (coefficientStep j) coefficientSpace := by
  intro n s k hk
  let N := ((BoundedIterate.inputEncoding coefficientStateEncoding).encode (n,s)).length
  have hn : N=2*n+1+(coefficientStateEncoding.encode s).length := by
    simp [N,BoundedIterate.inputEncoding,pairEncoding,UnaryBinary.unaryEncoding]
  have hs := coefficientStateEncoding_length s
  have hp : (polynomialEncoding.encode s.1).length≤N := by omega
  have hi : s.2.1≤N := by omega
  have hr : (rationalEncoding.encode s.2.2).length≤N := by omega
  have hkN : k≤N := by omega
  have ha : rationalBitHeight s.2.2≤N+1 := (rational_height_input _).trans (by omega)
  have hb := coefficient_acc_height j s k
  have hc := rationalEncoding_length_le_height (((coefficientStep j)^[k] s).2.2)
  have hm : k*((polynomialEncoding.encode s.1).length+3)≤N*(N+3) :=
    Nat.mul_le_mul hkN (by omega)
  have hl := coefficientStateEncoding_length (((coefficientStep j)^[k]) s)
  rw [coefficient_polynomial_iterate,coefficient_index_iterate] at hl
  change _≤coefficientSpace.eval N
  simp only [coefficientSpace,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_pow,Polynomial.eval_X]
  nlinarith

def sparseCoefficient (j : ℕ) (p : RationalPolynomialCode) : ℚ :=
  (p.map (selectedCoefficient j)).sum

theorem sparse_drop (j i : ℕ) (p : RationalPolynomialCode) :
    sparseCoefficient j (p.drop i)=selectedCoefficient j (p.getD i (0,0))+
      sparseCoefficient j (p.drop (i+1)) := by
  induction p generalizing i with
  | nil => simp [sparseCoefficient,selectedCoefficient]
  | cons t p ih =>
    cases i with
    | zero => simp [sparseCoefficient]
    | succ i => simpa using ih i

theorem coefficient_invariant (j : ℕ) (s : CoefficientState) (k : ℕ) :
    (((coefficientStep j)^[k] s).2.2)+
      sparseCoefficient j ((((coefficientStep j)^[k] s).1).drop
        (((coefficientStep j)^[k] s).2.1))=
      s.2.2+sparseCoefficient j (s.1.drop s.2.1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    change (((coefficientStep j)^[k] s).2.2)+
      selectedCoefficient j ((((coefficientStep j)^[k] s).1).getD
        (((coefficientStep j)^[k] s).2.1) (0,0))+
      sparseCoefficient j ((((coefficientStep j)^[k] s).1).drop
        (((coefficientStep j)^[k] s).2.1+1))= _
    rw [add_assoc,← sparse_drop]
    exact ih

theorem sparseCoefficient_polynomial (j : ℕ) (p : RationalPolynomialCode) :
    sparseCoefficient j p=p.polynomial.coeff j := by
  induction p with
  | nil => simp [sparseCoefficient,RationalPolynomialCode.polynomial]
  | cons t p ih =>
    simp only [sparseCoefficient,List.map_cons,List.sum_cons,
      RationalPolynomialCode.polynomial,Polynomial.coeff_add,Polynomial.coeff_monomial]
    rw [← ih]
    simp [selectedCoefficient,eq_comm,sparseCoefficient]

/-- Polynomial-time coefficient reading has no degree or canonical-list promise. -/
def sparseCoefficientComputes (j : ℕ) :
    Computes polynomialEncoding rationalEncoding (sparseCoefficient j) := by
  let start : Computes polynomialEncoding coefficientStateEncoding (fun p => (p,0,0)) :=
    pairComputes (identityComputes polynomialEncoding)
      (pairComputes (constantComputes polynomialEncoding UnaryBinary.unaryEncoding 0)
        (constantComputes polynomialEncoding rationalEncoding 0))
  let rounds := Lists.lengthUnaryComputes sparseTermEncoding
  let loop := BoundedIterate.computes coefficientStateEncoding (coefficientStep j)
    (coefficientStepComputes j) coefficientSpace (coefficient_intermediate j)
  let extract := (Wiring.secondComputes polynomialEncoding
    (pairEncoding UnaryBinary.unaryEncoding rationalEncoding)).andThen
      (Wiring.secondComputes UnaryBinary.unaryEncoding rationalEncoding)
  apply congrComputes (((pairComputes rounds start).andThen loop).andThen extract)
  intro p
  have h := coefficient_invariant j (p,0,0) p.length
  rw [coefficient_polynomial_iterate,coefficient_index_iterate] at h
  simpa only [Function.comp_apply,List.drop_length,List.drop_zero,Nat.zero_add,
    sparseCoefficient,List.map_nil,List.sum_nil,add_zero,zero_add] using h

end
end Paper2.ExactInput.FixedRootCodec
