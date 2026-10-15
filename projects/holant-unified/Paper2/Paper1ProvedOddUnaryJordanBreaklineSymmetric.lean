import Paper2.Paper1ProvedOddUnaryOneHotLineVisibility
import Paper2.Paper1ProvedOddUnaryNRJordanPowers

/-! A binary breaking an isotropic Jordan line supplies a nonsingular
symmetric trace-zero matrix, possibly after a Jordan congruence. -/
namespace Paper2.Paper1Proved.OddUnary.JordanBreaklineSymmetric
open Holant
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {K : Type} [Field K] [CharZero K]

def trace (T : Bool→Bool→K) : K:=T false false+T true true

def gramLeft (T : Bool→Bool→K) : Bool→Bool→K:=
  fun i j=>∑k:Bool,T k i*T k j

def gramRight (T : Bool→Bool→K) : Bool→Bool→K:=
  fun i j=>∑k:Bool,T i k*T j k

def pencil (t z : K) : Bool→Bool→K:=
  fun i j=>(if i=j then 1 else 0)+z*NRJordanPowers.repeated t i*NRJordanPowers.repeated t j

def congruence (P S : Bool→Bool→K) : Bool→Bool→K:=
  fun i j=>∑a:Bool,∑b:Bool,P a i*S a b*P b j

theorem gramLeft_symmetric (T : Bool→Bool→K) : ∀i j,gramLeft T i j=gramLeft T j i := by
  intro i j
  simp only [gramLeft,Fintype.sum_bool]
  ring

theorem gramRight_symmetric (T : Bool→Bool→K) : ∀i j,gramRight T i j=gramRight T j i := by
  intro i j
  simp only [gramRight,Fintype.sum_bool]
  ring

theorem gramLeft_determinant (T : Bool→Bool→K) :
    OneHotBinaryProjection.determinant (gramLeft T)=OneHotBinaryProjection.determinant T^2 := by
  simp only [OneHotBinaryProjection.determinant,gramLeft,Fintype.sum_bool]
  ring

theorem gramRight_determinant (T : Bool→Bool→K) :
    OneHotBinaryProjection.determinant (gramRight T)=OneHotBinaryProjection.determinant T^2 := by
  simp only [OneHotBinaryProjection.determinant,gramRight,Fintype.sum_bool]
  ring

theorem zero_grams_trace_symmetric (t : K) (iso : t^2=-1) (T : Bool→Bool→K)
    (live : OneHotLineProjection.line (NRJordanPowers.repeated t) T≠0)
    (left : OneHotLineProjection.line (NRJordanPowers.repeated t) (gramLeft T)=0)
    (right : OneHotLineProjection.line (NRJordanPowers.repeated t) (gramRight T)=0) :
    trace T=0 ∧ ∀i j,T i j=T j i := by
  have tnz : t≠0 := by intro zero;rw [zero,zero_pow (by decide)] at iso;norm_num at iso
  let q:=OneHotLineProjection.line (NRJordanPowers.repeated t) T
  have qform : q=T false false-T true true+t*(T false true+T true false) := by
    simp only [q,OneHotLineProjection.line,LinearMap.coe_mk,AddHom.coe_mk,
      NRJordanPowers.repeated,Bool.false_eq_true,ite_true,ite_false]
    linear_combination T true true*iso
  have l : q*(trace T+t*(T false true-T true false))=0 := by
    rw [qform]
    simp only [trace]
    simp only [OneHotLineProjection.line,LinearMap.coe_mk,AddHom.coe_mk,
      NRJordanPowers.repeated,gramLeft,Fintype.sum_bool,
      Bool.false_eq_true,ite_true,ite_false] at left
    linear_combination left-(T true false^2+T true true^2)*iso
  have r : q*(trace T-t*(T false true-T true false))=0 := by
    rw [qform]
    simp only [trace]
    simp only [OneHotLineProjection.line,LinearMap.coe_mk,AddHom.coe_mk,
      NRJordanPowers.repeated,gramRight,Fintype.sum_bool,
      Bool.false_eq_true,ite_true,ite_false] at right
    linear_combination right-(T false true^2+T true true^2)*iso
  have ll:= (mul_eq_zero.mp l).resolve_left live
  have rr:= (mul_eq_zero.mp r).resolve_left live
  have tr : trace T=0 := by
    have twice : (2:K)*trace T=0 := by linear_combination ll+rr
    exact (mul_eq_zero.mp twice).resolve_left (by norm_num)
  have sym : T false true=T true false := by
    have twice : (2:K)*t*(T false true-T true false)=0 := by linear_combination ll-rr
    exact sub_eq_zero.mp ((mul_eq_zero.mp twice).resolve_left (mul_ne_zero (by norm_num) tnz))
  refine ⟨tr,?_⟩
  intro i j
  cases i <;> cases j
  · rfl
  · exact sym
  · exact sym.symm
  · rfl

theorem congruence_symmetric (P S : Bool→Bool→K) (hs : ∀i j,S i j=S j i) :
    ∀i j,congruence P S i j=congruence P S j i := by
  intro i j
  simp only [congruence,Fintype.sum_bool]
  rw [hs false true]
  ring

theorem pencil_determinant (t z : K) (iso : t^2=-1) :
    OneHotBinaryProjection.determinant (pencil t z)=1 := by
  simp only [pencil,OneHotBinaryProjection.determinant,NRJordanPowers.repeated,
    Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
  linear_combination z*iso

theorem congruence_determinant (P S : Bool→Bool→K) :
    OneHotBinaryProjection.determinant (congruence P S)=
      OneHotBinaryProjection.determinant P^2*OneHotBinaryProjection.determinant S := by
  simp only [congruence,OneHotBinaryProjection.determinant,Fintype.sum_bool]
  ring

theorem pencil_trace (t z : K) (iso : t^2=-1) (S : Bool→Bool→K) :
    trace (congruence (pencil t z) S)=
      trace S+2*z*OneHotLineProjection.line (NRJordanPowers.repeated t) S := by
  simp only [trace,congruence,pencil,OneHotLineProjection.line,LinearMap.coe_mk,AddHom.coe_mk,
    NRJordanPowers.repeated,Fintype.sum_bool,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false]
  linear_combination z^2*(S false false+t*S false true+t*S true false+t^2*S true true)*iso

theorem tracezero_pencil (t : K) (iso : t^2=-1) (S : Bool→Bool→K)
    (live : OneHotLineProjection.line (NRJordanPowers.repeated t) S≠0) :
    trace (congruence (pencil t (-trace S/(2*OneHotLineProjection.line
      (NRJordanPowers.repeated t) S))) S)=0 := by
  rw [pencil_trace t _ iso S]
  field_simp [live]
  ring

/-- The two alternatives retain their literal matrix recipes: either T
itself is symmetric trace zero, or a Gram matrix and one Jordan pencil
produce the required symmetric trace-zero congruence. -/
theorem tracezero_recipe (t : K) (iso : t^2=-1) (T : Bool→Bool→K)
    (live : OneHotLineProjection.line (NRJordanPowers.repeated t) T≠0) :
    (trace T=0 ∧ ∀i j,T i j=T j i) ∨
      ∃left:Bool,∃z:K,
        let S:=if left then gramLeft T else gramRight T
        trace (congruence (pencil t z) S)=0 ∧
        (∀i j,congruence (pencil t z) S i j=congruence (pencil t z) S j i) ∧
        OneHotBinaryProjection.determinant (congruence (pencil t z) S)=
          OneHotBinaryProjection.determinant T^2 := by
  classical
  by_cases hl : OneHotLineProjection.line (NRJordanPowers.repeated t) (gramLeft T)=0
  · by_cases hr : OneHotLineProjection.line (NRJordanPowers.repeated t) (gramRight T)=0
    · exact Or.inl (zero_grams_trace_symmetric t iso T live hl hr)
    · right
      refine ⟨false,-trace (gramRight T)/(2*OneHotLineProjection.line
        (NRJordanPowers.repeated t) (gramRight T)),?_,?_,?_⟩
      · exact tracezero_pencil t iso _ hr
      · exact congruence_symmetric _ _ (gramRight_symmetric T)
      · rw [congruence_determinant,pencil_determinant t _ iso,one_pow,one_mul]
        simp only [Bool.false_eq_true,ite_false,gramRight_determinant]
  · right
    refine ⟨true,-trace (gramLeft T)/(2*OneHotLineProjection.line
      (NRJordanPowers.repeated t) (gramLeft T)),?_,?_,?_⟩
    · exact tracezero_pencil t iso _ hl
    · exact congruence_symmetric _ _ (gramLeft_symmetric T)
    · rw [congruence_determinant,pencil_determinant t _ iso,one_pow,one_mul]
      simp only [ite_true,gramLeft_determinant]

end
end Paper2.Paper1Proved.OddUnary.JordanBreaklineSymmetric

