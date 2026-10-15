import Paper2.DegreeCSP.BooleanMinimalFace
import Paper2.DegreeCSP.AxisRatioSigns
import Paper2.DegreeCSP.BinaryPhaseChart

/-! A nontrivial normalized sign in a full-support separable-weight table has
an actual two-coordinate binary restriction with negative cross product and
nonzero determinant. This is pure coefficient algebra, with no generation or
BO premise. -/
namespace Paper2.DegreeCSP.FullSupportBinaryWitness
open scoped BigOperators
open Tractable AxisRatioSigns
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {n : ℕ}

/-- The original literal coefficient table restricted to two actual coordinates. -/
def coefficientTable (f : Signature AlgebraicComplex n) (z : Fin n→Bool)
    (i j : Fin n) : Signature AlgebraicComplex 2 := fun x =>
  f (Function.update (Function.update z i (x 0)) j (x 1))

/-- Separable coordinate weights have equal products on opposite face corners. -/
theorem wordFactor_rectangle (φ : Fin n→AlgebraicComplex) (z : Fin n→Bool)
    (i j : Fin n) (hij : i≠j) :
    wordFactor φ (Function.update (Function.update z i false) j false) *
      wordFactor φ (Function.update (Function.update z i true) j true) =
    wordFactor φ (Function.update (Function.update z i false) j true) *
      wordFactor φ (Function.update (Function.update z i true) j false) := by
  classical
  simp only [wordFactor,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro l _
  by_cases hli : l=i
  · subst l
    simp [Function.update,hij,mul_comm]
  · by_cases hlj : l=j
    · subst l
      simp [Function.update,mul_comm]
    · simp [Function.update,hli,hlj]

private theorem boolValue_injective :
    Function.Injective (fun b : Bool => (if b then 1 else 0 : ZMod 2)) := by
  intro a b h
  cases a <;> cases b <;> simp_all

/-- A nonzero binary off-diagonal product and a negative cross relation force
a nonzero determinant in the actual complex coefficient field. -/
theorem negative_cross_determinant (G : Bool→Bool→ℂ)
    (hne : ∀ b d,G b d≠0)
    (hneg : G false false*G true true= -(G false true*G true false)) :
    OriginalBO.binaryDeterminant G≠0 := by
  intro hz
  unfold OriginalBO.binaryDeterminant at hz
  rw [hneg] at hz
  have hzero : (2 : ℂ)*(G false true*G true false)=0 := by
    linear_combination -hz
  exact (mul_ne_zero (by norm_num) (mul_ne_zero (hne false true) (hne true false))) hzero

/-- The witness contains the exact restricted table, its full support, its
negative cross equation, and its original complex determinant. -/
theorem exists_signed_binary (f : Signature AlgebraicComplex n)
    (c : AlgebraicComplex) (hc : c≠0) (φ : Fin n→AlgebraicComplex)
    (hφ : ∀ i,φ i≠0) (P : (Fin n→Bool)→Bool)
    (hzero : P zeroWord=false)
    (haxes : ∀ i,P (Function.update zeroWord i true)=false)
    (hex : ∃ x,P x=true)
    (hdisplay : ∀ x,f x=c*wordFactor φ x*(if P x then -1 else 1)) :
    ∃ z i j,i≠j ∧
      (∀ x,coefficientTable f z i j x≠0) ∧
      (coefficientTable f z i j ![false,false]*coefficientTable f z i j ![true,true] =
        -(coefficientTable f z i j ![false,true]*coefficientTable f z i j ![true,false])) ∧
      OriginalBO.binaryDeterminant
        (fun b d => (coefficientTable f z i j ![b,d] : ℂ))≠0 := by
  classical
  let Q : Holant.Tractable.AffinePhase.Word n→ZMod 2 := fun x=>if P x then 1 else 0
  have hQzero : Q (Holant.Tractable.AffinePhase.origin n)=0 := by
    change (if P zeroWord then 1 else 0)=0
    simp [hzero]
  have hQaxes : ∀ i,Q (Function.update (Holant.Tractable.AffinePhase.origin n) i true)=0 := by
    intro i
    change (if P (Function.update zeroWord i true) then 1 else 0)=0
    simp [haxes]
  have hQex : ∃ x,Q x=1 := by
    obtain ⟨x,hx⟩ := hex
    exact ⟨x,by simp [Q,hx]⟩
  obtain ⟨z,i,j,hij,hface⟩ := BooleanMinimalFace.exists_and_face Q hQzero hQaxes hQex
  have hbool (b d : Bool) : P (Function.update (Function.update z i b) j d)=(b&&d) :=
    boolValue_injective (hface b d)
  have hfull (x : Fin n→Bool) : f x≠0 := by
    rw [hdisplay]
    apply mul_ne_zero (mul_ne_zero hc (wordFactor_ne_zero φ hφ x))
    cases P x <;> simp
  have htable : ∀ x,coefficientTable f z i j x≠0 := fun x=>hfull _
  have hneg : coefficientTable f z i j ![false,false]*coefficientTable f z i j ![true,true] =
      -(coefficientTable f z i j ![false,true]*coefficientTable f z i j ![true,false]) := by
    change f (Function.update (Function.update z i false) j false)*
      f (Function.update (Function.update z i true) j true) =
      -(f (Function.update (Function.update z i false) j true)*
        f (Function.update (Function.update z i true) j false))
    simp only [hdisplay,hbool,Bool.false_and,Bool.and_false,
      Bool.and_self,Bool.false_eq_true,ite_false,ite_true,mul_one]
    linear_combination -c^2 * wordFactor_rectangle φ z i j hij
  refine ⟨z,i,j,hij,htable,hneg,?_⟩
  apply negative_cross_determinant
  · intro b d
    exact_mod_cast htable ![b,d]
  · exact_mod_cast hneg

end
end Paper2.DegreeCSP.FullSupportBinaryWitness
