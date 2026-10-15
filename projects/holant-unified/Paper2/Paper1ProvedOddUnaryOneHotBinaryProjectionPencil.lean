import Holant.Proofs.FiniteGroups.Stabilization.BinaryPrimes
import Mathlib.Algebra.Polynomial.Roots

/-! Simultaneous nonvanishing for literal binary projection pencils over
the unchanged coefficient field. A single parameter avoids both the
determinant zeros and the displayed 11-entry zeros. -/
namespace Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection
open Holant
open Polynomial
noncomputable section
variable {K : Type} [Field K]

def determinant (M : Bool → Bool → K) : K :=
  M false false*M true true-M false true*M true false

def mixed (S U : Bool → Bool → K) : K :=
  S false false*U true true+U false false*S true true-
    S false true*U true false-U false true*S true false

def combination (S U : Bool → Bool → K) (a b : K) : Bool → Bool → K :=
  fun i j => a*S i j+b*U i j

def determinantPolynomial (S U : Bool → Bool → K) : K[X] :=
  C (determinant U)*X^2+C (mixed S U)*X+C (determinant S)

theorem determinant_combination (S U : Bool → Bool → K) (a b : K) :
    determinant (combination S U a b)=
      a^2*determinant S+a*b*mixed S U+b^2*determinant U := by
  simp only [determinant,combination,mixed]
  ring

theorem determinantPolynomial_eval (S U : Bool → Bool → K) (z : K) :
    (determinantPolynomial S U).eval z=determinant (combination S U 1 z) := by
  rw [determinant_combination]
  simp only [determinantPolynomial,eval_add,eval_mul,eval_C,eval_pow,eval_X]
  ring

theorem determinantPolynomial_nonzero (S U : Bool → Bool → K)
    (nonsingular : ∃ a b,determinant (combination S U a b)≠0) :
    determinantPolynomial S U≠0 := by
  intro zero
  obtain ⟨a,b,live⟩ := nonsingular
  have h0 := congrArg (fun p : K[X] => p.coeff 0) zero
  have h1 := congrArg (fun p : K[X] => p.coeff 1) zero
  have h2 := congrArg (fun p : K[X] => p.coeff 2) zero
  simp [determinantPolynomial] at h0 h1 h2
  apply live
  rw [determinant_combination,h0,h1,h2]
  ring

theorem entryPolynomial_nonzero (a b : K) (live : a≠0 ∨ b≠0) :
    (C a+C b*X : K[X])≠0 := by
  intro zero
  have h0 := congrArg (fun p : K[X] => p.coeff 0) zero
  have h1 := congrArg (fun p : K[X] => p.coeff 1) zero
  simp at h0 h1
  rcases live with live|live
  · exact live h0
  · exact live h1

/-- Singularities at the three original-field projective samples determine
all coefficients. A nonsingular extension-field sample therefore descends
to one of these three original-field samples. -/
theorem descend_nonsingular {L : Type} [Field L] (phi : K →+* L)
    (S U : Bool → Bool → K)
    (nonsingular : ∃ a b : L,determinant
      (combination (fun i j => phi (S i j)) (fun i j => phi (U i j)) a b)≠0) :
    ∃ a b : K,determinant (combination S U a b)≠0 := by
  classical
  by_contra bad
  push Not at bad
  have h0 : determinant S=0 := by simpa [determinant,combination] using bad 1 0
  have h1 : determinant U=0 := by simpa [determinant,combination] using bad 0 1
  have hsum := bad 1 1
  have hm : mixed S U=0 := by
    rw [determinant_combination,h0,h1] at hsum
    simpa using hsum
  obtain ⟨a,b,live⟩ := nonsingular
  apply live
  rw [determinant_combination]
  have mapped0 : determinant (fun i j => phi (S i j))=0 := by
    rw [determinant,←map_mul,←map_mul,←map_sub]
    exact (congrArg phi h0).trans (map_zero phi)
  have mapped1 : determinant (fun i j => phi (U i j))=0 := by
    rw [determinant,←map_mul,←map_mul,←map_sub]
    exact (congrArg phi h1).trans (map_zero phi)
  have mappedMixed : mixed (fun i j => phi (S i j)) (fun i j => phi (U i j))=0 := by
    simpa only [mixed,map_sub,map_add,map_mul,map_zero] using congrArg phi hm
  rw [mapped0,mapped1,mappedMixed]
  ring

theorem combination_one (S U : Bool → Bool → K) (z : K) :
    combination S U 1 z=S+z • U := by
  funext i j
  simp [combination]

/-- The displayed entry can be replaced by any fixed original-field
linear functional, including pairing against an actual isotropic line. -/
theorem select_pencil_linear [Infinite K] (S U : Bool → Bool → K)
    (L : (Bool → Bool → K) →ₗ[K] K)
    (visible : L S≠0 ∨ L U≠0)
    (nonsingular : ∃ a b,determinant (combination S U a b)≠0) :
    ∃ z : K,L (combination S U 1 z)≠0 ∧
      determinant (combination S U 1 z)≠0 := by
  classical
  let p := determinantPolynomial S U
  let q : K[X] := C (L S)+C (L U)*X
  have pnz : p≠0 := determinantPolynomial_nonzero S U nonsingular
  have qnz : q≠0 := entryPolynomial_nonzero _ _ visible
  have product : p*q≠0 := mul_ne_zero pnz qnz
  have available : ∃ z : K,(p*q).eval z≠0 := by
    by_contra bad
    push Not at bad
    exact product (Polynomial.zero_of_eval_zero _ bad)
  obtain ⟨z,live⟩ := available
  rw [eval_mul] at live
  have plive := (mul_ne_zero_iff.mp live).1
  have qlive := (mul_ne_zero_iff.mp live).2
  refine ⟨z,?_,?_⟩
  · rw [combination_one,map_add,map_smul,smul_eq_mul]
    simpa only [q,eval_add,eval_C,eval_mul,eval_X,mul_comm (L U) z] using qlive
  · exact (determinantPolynomial_eval S U z) ▸ plive

/-- Genuine original-field selection from two independent projection
coefficients, preserving both desired nonvanishing conditions. -/
theorem select_pencil [Infinite K] (S U : Bool → Bool → K)
    (entry : S true true≠0 ∨ U true true≠0)
    (nonsingular : ∃ a b,determinant (combination S U a b)≠0) :
    ∃ z : K,combination S U 1 z true true≠0 ∧
      determinant (combination S U 1 z)≠0 := by
  classical
  let p := determinantPolynomial S U
  let q : K[X] := C (S true true)+C (U true true)*X
  have pnz : p≠0 := determinantPolynomial_nonzero S U nonsingular
  have qnz : q≠0 := entryPolynomial_nonzero _ _ entry
  have product : p*q≠0 := mul_ne_zero pnz qnz
  have available : ∃ z : K,(p*q).eval z≠0 := by
    by_contra bad
    push Not at bad
    exact product (Polynomial.zero_of_eval_zero _ bad)
  obtain ⟨z,live⟩ := available
  rw [eval_mul] at live
  have plive := (mul_ne_zero_iff.mp live).1
  have qlive := (mul_ne_zero_iff.mp live).2
  refine ⟨z,?_,?_⟩
  · simpa only [q,eval_add,eval_C,eval_mul,eval_X,combination,one_mul,
      mul_comm (U true true) z] using qlive
  · exact (determinantPolynomial_eval S U z) ▸ plive

end
end Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection

