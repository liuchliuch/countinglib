import Paper2.ExactInput.FixedRootCodec.BisectionMachine
import Paper2.ExactInput.FixedRootCodec.VariablePolynomial
import Paper2.ExactInput.FixedRootCodec.ReverseRounding

/-! A varying-polynomial rank bisection controller. The root-count function
is executed through its supplied concrete Boolean-stack program; it is never
installed as an arithmetic primitive. The fixed rank selects the lower half
exactly when the number of roots at or below the midpoint does not exceed the
rank. A common integer denominator prevents excessive intermediate bit growth.
Every input state, including an invalid bracket, satisfies the proved bound. -/
namespace Paper2.ExactInput.FixedRootCodec.VariableRootBisection
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines GraphPreprocessing
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

abbrev CountFunction (n : ℕ) := (Fin n → ℚ) → ℚ → ℕ
abbrev State (n : ℕ) := (Fin n → ℚ) × BisectionState

def stateEncoding (n : ℕ) := pairEncoding (vectorEncoding n) bisectionEncoding

def countLeComputes (j : ℕ) : Computes encodingNatBool encodingBoolBool
    (fun c : ℕ => decide (c ≤ j)) := by
  let difference := rationalProvider.addComputes roundNaturalCastComputes
    (constantComputes encodingNatBool rationalEncoding (-((j+1 : ℕ) : ℚ)))
  apply congrComputes (difference.andThen rationalNegativeComputes)
  intro c
  have h : (c : ℚ) - ((j+1 : ℕ) : ℚ) < 0 ↔ c ≤ j := by
    rw [sub_lt_zero]
    exact_mod_cast Nat.lt_succ_iff
  change decide ((c : ℚ) + -((j+1 : ℕ) : ℚ) < 0) = decide (c ≤ j)
  simp only [← sub_eq_add_neg,h]

def half (lower : Bool) (s : BisectionState) : BisectionState :=
  if lower then (s.1+s.2.1,s.2.1+s.2.1,2*s.2.2)
  else (s.1+s.1,s.1+s.2.1,2*s.2.2)

def step (count : CountFunction n) (j : ℕ) (s : State n) : State n :=
  (s.1,half (decide (count s.1 (midpoint s.2) ≤ j)) s.2)

def stepComputes (count : CountFunction n) (j : ℕ)
    (w : Computes (VariablePolynomial.inputEncoding n) encodingNatBool
      (fun p => count p.1 p.2)) :
    Computes (stateEncoding n) (stateEncoding n) (step count j) := by
  let coefficients := Wiring.firstComputes (vectorEncoding n) bisectionEncoding
  let bracket := Wiring.secondComputes (vectorEncoding n) bisectionEncoding
  let middle := bracket.andThen midpointComputes
  let test := ((pairComputes coefficients middle).andThen w).andThen (countLeComputes j)
  let lower := bracket.andThen
    (pairComputes sumComputes (pairComputes doubleRightComputes doubleDenominatorComputes))
  let upper := bracket.andThen
    (pairComputes doubleLeftComputes (pairComputes sumComputes doubleDenominatorComputes))
  exact congrComputes (pairComputes coefficients (ifComputes test lower upper))
    (fun s => by simp only [step,half,Function.comp_apply,decide_eq_true_eq])

@[simp] theorem step_coefficients (count : CountFunction n) (j : ℕ) (s : State n) :
    (step count j s).1 = s.1 := rfl

@[simp] theorem half_denominator (lower : Bool) (s : BisectionState) :
    (half lower s).2.2 = 2*s.2.2 := by cases lower <;> rfl

@[simp] theorem step_denominator (count : CountFunction n) (j : ℕ) (s : State n) :
    (step count j s).2.2.2 = 2*s.2.2.2 := half_denominator _ _

theorem half_abs_bound (lower : Bool) (s : BisectionState) (M : ℕ)
    (hl : s.1.natAbs ≤ M) (hu : s.2.1.natAbs ≤ M) :
    (half lower s).1.natAbs ≤ 2*M ∧ (half lower s).2.1.natAbs ≤ 2*M := by
  have hs := (Int.natAbs_add_le s.1 s.2.1).trans (Nat.add_le_add hl hu)
  have hll := (Int.natAbs_add_le s.1 s.1).trans (Nat.add_le_add hl hl)
  have huu := (Int.natAbs_add_le s.2.1 s.2.1).trans (Nat.add_le_add hu hu)
  cases lower <;> simp only [half,Bool.false_eq_true,↓reduceIte] <;> constructor <;> omega

theorem iterate_coefficients (count : CountFunction n) (j : ℕ) (s : State n) (k : ℕ) :
    ((step count j)^[k] s).1 = s.1 := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [Function.iterate_succ_apply',step_coefficients] using ih

theorem iterate_denominator (count : CountFunction n) (j : ℕ) (s : State n) (k : ℕ) :
    ((step count j)^[k] s).2.2.2 = 2^k*s.2.2.2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',step_denominator,ih,pow_succ]
    ring

theorem iterate_abs_bound (count : CountFunction n) (j : ℕ) (s : State n)
    (M : ℕ) (hl : s.2.1.natAbs ≤ M) (hu : s.2.2.1.natAbs ≤ M) (k : ℕ) :
    (((step count j)^[k] s).2.1).natAbs ≤ 2^k*M ∧
      (((step count j)^[k] s).2.2.1).natAbs ≤ 2^k*M := by
  induction k with
  | zero => simpa using And.intro hl hu
  | succ k ih =>
    have h := half_abs_bound
      (decide (count ((step count j)^[k] s).1 (midpoint ((step count j)^[k] s).2) ≤ j))
      ((step count j)^[k] s).2 (2^k*M) ih.1 ih.2
    simpa only [Function.iterate_succ_apply',step,pow_succ,Nat.mul_assoc,Nat.mul_comm,
      Nat.mul_left_comm] using h

theorem bracket_prefix_length (count : CountFunction n) (j : ℕ) (s : State n) (k : ℕ) :
    (bisectionEncoding.encode ((step count j)^[k] s).2).length ≤
      5*k+5*(bisectionEncoding.encode s.2).length+15 := by
  let L := (bisectionEncoding.encode s.2).length
  let M := max s.2.1.natAbs s.2.2.1.natAbs
  have hlen := bisectionEncoding_length s.2
  have hl : (IntegerArithmetic.encoding.encode s.2.1).length ≤ L := by omega
  have hu : (IntegerArithmetic.encoding.encode s.2.2.1).length ≤ L := by omega
  have hq : s.2.2.2.size ≤ L := by rw [← encodeNat_length]; omega
  have hMl : s.2.1.natAbs.size ≤ L+1 := (integer_abs_size_le _).trans (by omega)
  have hMu : s.2.2.1.natAbs.size ≤ L+1 := (integer_abs_size_le _).trans (by omega)
  have hM : M.size ≤ L+1 :=
    Nat.size_le.mpr (max_lt (Nat.size_le.mp hMl) (Nat.size_le.mp hMu))
  have hb := iterate_abs_bound count j s M (le_max_left _ _) (le_max_right _ _) k
  have hp := natSize_mul_le (2^k) M
  rw [Nat.size_pow] at hp
  have hleft : (((step count j)^[k] s).2.1).natAbs.size ≤ k+L+2 :=
    (Nat.size_le_size hb.1).trans (hp.trans (by omega))
  have hright : (((step count j)^[k] s).2.2.1).natAbs.size ≤ k+L+2 :=
    (Nat.size_le_size hb.2).trans (hp.trans (by omega))
  have hd : (((step count j)^[k] s).2.2.2).size ≤ k+L+1 := by
    rw [iterate_denominator]
    have h := natSize_mul_le (2^k) s.2.2.2
    rw [Nat.size_pow] at h
    omega
  have bl := (integer_bits_le (((step count j)^[k] s).2.1)).trans
    (Nat.add_le_add_right hleft 1)
  have bu := (integer_bits_le (((step count j)^[k] s).2.2.1)).trans
    (Nat.add_le_add_right hright 1)
  rw [bisectionEncoding_length,encodeNat_length]
  omega

def space : Polynomial ℕ := 5*Polynomial.X+20

theorem intermediate (count : CountFunction n) (j : ℕ) :
    BoundedIterate.IntermediateBound (stateEncoding n) (step count j) space := by
  intro k s r hr
  have hb := bracket_prefix_length count j s r
  have hc := iterate_coefficients count j s r
  let C := ((vectorEncoding n).encode s.1).length
  let B := (bisectionEncoding.encode s.2).length
  have he : ((stateEncoding n).encode ((step count j)^[r] s)).length =
      2*C+1+(bisectionEncoding.encode ((step count j)^[r] s).2).length := by
    simp only [stateEncoding,pairEncoding_length,hc,C]
  have hi : ((BoundedIterate.inputEncoding (stateEncoding n)).encode (k,s)).length =
      2*k+2*C+B+2 := by
    simp only [BoundedIterate.inputEncoding,stateEncoding,pairEncoding_length,
      UnaryBinary.unaryEncoding,List.length_replicate,C,B]
    omega
  rw [he,hi]
  simp only [space,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
    Polynomial.eval_X]
  omega

/-- The actual unary-counted refinement program depends on the concrete root
count program and charges every invocation and intermediate serialization. -/
def computes (count : CountFunction n) (j : ℕ)
    (w : Computes (VariablePolynomial.inputEncoding n) encodingNatBool
      (fun p => count p.1 p.2)) :
    Computes (BoundedIterate.inputEncoding (stateEncoding n)) (stateEncoding n)
      (fun p => (step count j)^[p.1] p.2) :=
  BoundedIterate.computes (stateEncoding n) (step count j)
    (stepComputes count j w) space (intermediate count j)

end
end Paper2.ExactInput.FixedRootCodec.VariableRootBisection
