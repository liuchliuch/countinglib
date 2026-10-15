import Paper2.Paper1ProvedOddUnaryNRCapAlgebra
import Paper2.Paper1ProvedOddUnaryWEscapeBinary

/-! A ternary outside one fixed matching orientation has a literal ordinary
pin face outside that orientation. The fixed coordinate chart is kept in the
mathematical proof; every selected face uses original physical coordinates. -/
namespace Paper2.Paper1Proved.OddUnary.OneHotFaces
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.RemoteWork.TractChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def pin {K : Type} [Field K] (v : Bool) : Holant.Signature K 1 :=
  fun x => if x 0=v then 1 else 0

theorem pin_cap_inverse (R : InvertibleKernel) (f : Holant.Signature AlgebraicComplex 3)
    (i : Fin 3) (v : Bool) :
    R.symm.action (NR.cap (pin v) f i)=fun x =>
      R.matrix v false*(R.symm.action f) (i.insertNth false x)+
      R.matrix v true*(R.symm.action f) (i.insertNth true x) := by
  have form := NR.cap_action R.matrix (pin v) (R.symm.action f) i
  change NR.cap (pin v) (R.action (R.symm.action f)) i=R.action _ at form
  rw [R.action_symm_action] at form
  rw [form,R.symm_action_action]
  funext x
  simp only [NR.columnPair,pin,Fintype.sum_bool]
  cases v <;> simp <;> ring

private theorem scalars_zero (R : InvertibleKernel) (a b : AlgebraicComplex)
    (h0 : R.matrix false false*a+R.matrix false true*b=0)
    (h1 : R.matrix true false*a+R.matrix true true*b=0) : a=0 ∧ b=0 := by
  have hd := SymmetricBinaryPullback.determinant_ne_zero R
  have ha : SymmetricBinaryPullback.determinant R.matrix*a=0 := by
    unfold SymmetricBinaryPullback.determinant
    linear_combination R.matrix true true*h0-R.matrix false true*h1
  have hb : SymmetricBinaryPullback.determinant R.matrix*b=0 := by
    unfold SymmetricBinaryPullback.determinant
    linear_combination R.matrix false false*h1-R.matrix true false*h0
  exact ⟨(mul_eq_zero.mp ha).resolve_left hd,(mul_eq_zero.mp hb).resolve_left hd⟩

/-- Both original physical pin faces detect every coordinate slice; the
invertible chart cannot hide their joint support. -/
theorem chart_coefficients_zero (R : InvertibleKernel) (f : Holant.Signature AlgebraicComplex 3)
    (faces : ∀ i : Fin 3,∀ v : Bool,
      Holant.Signature.OneHot (R.symm.action (NR.cap (pin v) f i))) :
    ∀ i : Fin 3,∀ v : Bool,(R.symm.action f) (i.insertNth v ![true,true])=0 := by
  intro i v
  have h0 := faces i false ![true,true] (by decide)
  have h1 := faces i true ![true,true] (by decide)
  rw [pin_cap_inverse] at h0 h1
  have h := scalars_zero R _ _ h0 h1
  cases v
  · exact h.1
  · exact h.2

private theorem word_eq (x : Fin 3 → Bool) : x=![x 0,x 1,x 2] := by
  funext i
  fin_cases i <;> rfl

/-- All six physical binary pin faces inside the common matching image force
literal one-hot support in that same common chart. -/
theorem oneHot_of_faces (R : InvertibleKernel) (f : Holant.Signature AlgebraicComplex 3)
    (faces : ∀ i : Fin 3,∀ v : Bool,
      Holant.Signature.OneHot (R.symm.action (NR.cap (pin v) f i))) :
    Holant.Signature.OneHot (R.symm.action f) := by
  have zeros := chart_coefficients_zero R f faces
  intro x high
  have hx := word_eq x
  rw [hx] at high ⊢
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2
  all_goals simp only [h0,h1,h2] at high ⊢
  · exact ((by decide : ¬1<Holant.weight (![false,false,false] : Fin 3 → Bool)) high).elim
  · exact ((by decide : ¬1<Holant.weight (![false,false,true] : Fin 3 → Bool)) high).elim
  · exact ((by decide : ¬1<Holant.weight (![false,true,false] : Fin 3 → Bool)) high).elim
  · simpa using zeros 0 false
  · exact ((by decide : ¬1<Holant.weight (![true,false,false] : Fin 3 → Bool)) high).elim
  · have e : (1 : Fin 3).insertNth false ![true,true]=(![true,false,true] : Fin 3 → Bool) := by decide
    simpa only [e] using zeros 1 false
  · have e : (2 : Fin 3).insertNth false ![true,true]=(![true,true,false] : Fin 3 → Bool) := by decide
    simpa only [e] using zeros 2 false
  · simpa using zeros 0 true

/-- The selected cap is one of the two literal physical pins, before any
Jordan interpolation or finite-table extension is performed. -/
theorem exists_outside_face (R : InvertibleKernel) (f : Holant.Signature AlgebraicComplex 3)
    (outside : ¬Holant.Signature.OneHot (R.symm.action f)) :
    ∃ i : Fin 3,∃ v : Bool,
      ¬Holant.Signature.OneHot (R.symm.action (NR.cap (pin v) f i)) := by
  classical
  by_contra none
  apply outside
  apply oneHot_of_faces R f
  intro i v h high
  by_contra bad
  exact none ⟨i,v,fun good => bad (good h high)⟩

end
end Paper2.Paper1Proved.OddUnary.OneHotFaces

