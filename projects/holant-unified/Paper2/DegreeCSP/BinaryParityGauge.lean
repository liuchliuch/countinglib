import Paper2.DegreeCSP.FourthRootClassification
import Mathlib.Tactic

/-! The exact extra phase equation of a once-used rank-two parity face.
Fourth-root relatives alone do not imply affinity: the squared cross ratio
must be one. A weight twist changes that squared cross by precisely the
phase on the XOR bundle. -/
namespace Paper2.DegreeCSP.BinaryParityGauge
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 600000

abbrev Table := Bool → Bool → AlgebraicComplex

def signature (A : Table) : Signature AlgebraicComplex 2 := fun x => A (x 0) (x 1)

def cross (A : Table) : AlgebraicComplex :=
  A false false*A true true/(A false true*A true false)

def bundleWeight (n1 n2 n12 : ℕ) (b c : Bool) : ℕ :=
  (if b then n1 else 0)+(if c then n2 else 0)+
    (if Bool.xor b c then n12 else 0)

def twist (A : Table) (psi : AlgebraicComplex) (n1 n2 n12 : ℕ) : Table :=
  fun b c => A b c*psi⁻¹^(bundleWeight n1 n2 n12 b c)

theorem cross_twist (A : Table) (psi : AlgebraicComplex) (hp : psi≠0)
    (n1 n2 n12 : ℕ) :
    cross (twist A psi n1 n2 n12)=cross A*psi^(2*n12) := by
  rw [two_mul,pow_add]
  simp [cross,twist,bundleWeight,pow_add,inv_pow]
  field_simp [hp]

theorem squared_cross_twist (A : Table) (psi : AlgebraicComplex) (hp : psi≠0)
    (n1 n2 n12 : ℕ) :
    cross (twist A psi n1 n2 n12)^2=cross A^2*(psi^4)^n12 := by
  rw [cross_twist A psi hp,mul_pow]
  congr 1
  rw [←pow_mul,←pow_mul]
  congr 1
  omega

private theorem quadratic_corners (Q : QuadraticPhase 2) :
    Q.eval ![false,false]=Q.constant ∧
    Q.eval ![true,false]=Q.constant+Q.linear 0 ∧
    Q.eval ![false,true]=Q.constant+Q.linear 1 ∧
    Q.eval ![true,true]=Q.constant+Q.linear 0+Q.linear 1+Q.mixed 0 1 := by
  simp [QuadraticPhase.eval,Fin.sum_univ_two,bitValue]
  ring

theorem affine_squared_cross (A : Table) (ha : ∀ b c,A b c≠0)
    (h : Affine (signature A)) : cross A^2=1 := by
  rcases h with hz|⟨s,hs,S,Q,he⟩
  · exact False.elim (ha false false (congrFun hz ![false,false]))
  have holds (b c : Bool) : S.Holds ![b,c] := by
    by_contra hn
    apply ha b c
    have hval := congrFun he ![b,c]
    simpa [signature,affineFormula,hn] using hval
  have value (b c : Bool) : A b c=s*fourthRootPhase (Q.eval ![b,c]) := by
    have hval := congrFun he ![b,c]
    simpa [signature,affineFormula,holds] using hval
  obtain ⟨h00,h10,h01,h11⟩ := quadratic_corners Q
  have hc : cross A=fourthRootPhase (Q.mixed 0 1) := by
    unfold cross
    rw [value false false,value true true,value false true,value true false,
      h00,h11,h01,h10]
    simp only [FourthRootClassification.phase_add]
    field_simp [hs,fourthRootPhase_ne_zero]
  rw [hc]
  rcases Q.even_mixed 0 1 (by decide) with hm|hm
  · rw [hm,fourthRootPhase_zero,one_pow]
  · rw [hm]
    change (imaginaryUnit^2)^2=1
    rw [imaginaryUnit_sq]
    ring

private def binaryPhase (q0 q1 : ZMod 4) (negative : Bool) : QuadraticPhase 2 where
  constant := 0
  linear := ![q0,q1]
  mixed := fun _ _ => if negative then 2 else 0
  even_mixed _ _ _ := by cases negative <;> simp

private theorem phase_two : fourthRootPhase (2 : ZMod 4)= -1 := imaginaryUnit_sq

private theorem phase_formula (q0 q1 : ZMod 4) (negative b c : Bool) :
    fourthRootPhase ((binaryPhase q0 q1 negative).eval ![b,c])=
      (if b then fourthRootPhase q0 else 1)*
      (if c then fourthRootPhase q1 else 1)*
      (if b && c && negative then (-1 : AlgebraicComplex) else 1) := by
  cases b <;> cases c <;> cases negative
  all_goals simp [binaryPhase,QuadraticPhase.eval,Fin.sum_univ_two,bitValue,
    FourthRootClassification.phase_add,phase_two]

/-- With actual fourth-root relatives on the full four-entry table, the
squared cross equation is sufficient and necessary for the affine class. -/
theorem affine_iff_squared_cross (A : Table) (ha : ∀ b c,A b c≠0)
    (hroot : ∀ b c,(A b c/A false false)^4=1) :
    Affine (signature A) ↔ cross A^2=1 := by
  constructor
  · exact affine_squared_cross A ha
  · intro hc
    obtain ⟨q0,hq0⟩ := FourthRootClassification.exists_phase (hroot true false)
    obtain ⟨q1,hq1⟩ := FourthRootClassification.exists_phase (hroot false true)
    have hsign : cross A=1 ∨ cross A= -1 := by
      have hz : (cross A-1)*(cross A+1)=0 := by
        calc
          _=cross A^2-1 := by ring
          _=0 := by rw [hc,sub_self]
      rcases mul_eq_zero.mp hz with h|h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (by linear_combination h)
    obtain ⟨negative,hnegative⟩ : ∃negative : Bool,
        cross A=if negative then -1 else 1 := by
      rcases hsign with h|h
      · exact ⟨false,h⟩
      · exact ⟨true,h⟩
    convert affine_formula (A false false) (AffineSystem.unconstrained 2)
      (binaryPhase q0 q1 negative) using 1
    funext x
    have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
    rw [hx]
    change A (x 0) (x 1)=_
    simp only [affineFormula,AffineSystem.unconstrained_holds,ite_true,phase_formula,hq0,hq1]
    cases h0 : x 0 <;> cases h1 : x 1
    all_goals simp only [Bool.false_eq_true,ite_false,ite_true,
      Bool.false_and,Bool.true_and,mul_one,one_mul]
    · field_simp [ha false false]
    · field_simp [ha false false]
    · have he : A true true=A false false*(A true false/A false false)*
          (A false true/A false false)*cross A := by
        unfold cross
        field_simp [ha false false,ha false true,ha true false]
      rw [he,hnegative]
      ring

theorem twist_affine_iff (A : Table) (psi : AlgebraicComplex) (hp : psi≠0)
    (n1 n2 n12 : ℕ) (ha : ∀ b c,A b c≠0)
    (hroot : ∀ b c,
      (twist A psi n1 n2 n12 b c/twist A psi n1 n2 n12 false false)^4=1) :
    Affine (signature (twist A psi n1 n2 n12)) ↔ cross A^2*(psi^4)^n12=1 := by
  have hn (b c : Bool) : twist A psi n1 n2 n12 b c≠0 :=
    mul_ne_zero (ha b c) (pow_ne_zero _ (inv_ne_zero hp))
  rw [affine_iff_squared_cross _ hn hroot,squared_cross_twist A psi hp]


end
end Paper2.DegreeCSP.BinaryParityGauge
