import Paper2.DegreeCSP.TwoWordContextDegrees
import Paper2.Charge

/-! The boundary incidence of an exact two-word context records the original
occupied-weight difference modulo k. These identities transport its common
cyclic phase back to the original coefficients, without taking their k-th
powers or changing their support. -/
namespace Paper2.DegreeCSP.TwoWordContext
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {n : ℕ} (x y : Fin n → Bool)

theorem forward_weight_balance :
    Fintype.card {i : Fin n // Forward x y i} + Paper2.weight x =
      Paper2.weight y + Fintype.card (Reverse x y) := by
  simp only [Paper2.weight,Fintype.card_subtype,Finset.card_filter]
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hx:x i <;> cases hy:y i <;> simp [Forward,hx,hy]

theorem boundary_weight_balance (t : ℕ) :
    boundaryCount x y t + Paper2.weight x =
      Paper2.weight y + (t+1)*Fintype.card (Reverse x y) := by
  have he := forward_weight_balance x y
  unfold boundaryCount
  rw [Nat.add_mul,one_mul]
  omega

theorem boundary_weight_balance_of_positive {k : ℕ} (hk : 0<k) :
    boundaryCount x y (k-1) + Paper2.weight x =
      Paper2.weight y + k*Fintype.card (Reverse x y) := by
  have ht : k-1+1=k := by omega
  simpa only [ht] using boundary_weight_balance x y (k-1)

/-- No division or negative natural exponent is needed to express the
original signed occupied-weight difference. -/
theorem cyclic_phase_weight {k : ℕ} (hk : 0<k)
    (theta : AlgebraicComplex) (hcycle : theta^k=1) :
    theta^(boundaryCount x y (k-1))*theta^(Paper2.weight x)=
      theta^(Paper2.weight y) := by
  rw [←pow_add,boundary_weight_balance_of_positive x y hk,pow_add,pow_mul,
    hcycle,one_pow,mul_one]

/-- The common phase at actual context degrees becomes one fourth-power
coordinate weight on every original occupied word. -/
theorem ratio_four_weight_twist {k : ℕ} (hk : 0<k)
    (theta psi a b : AlgebraicComplex) (hcycle : theta^k=1)
    (hroot : psi^4=theta) (ha : a≠0) (hb : b≠0)
    (hratio : (b/a)^4=theta^(boundaryCount x y (k-1))) :
    ((b*psi⁻¹^(Paper2.weight y))/(a*psi⁻¹^(Paper2.weight x)))^4=1 := by
  have htheta : theta≠0 := by
    intro he
    rw [he,zero_pow (Nat.ne_of_gt hk)] at hcycle
    exact zero_ne_one hcycle
  have hpsi : psi≠0 := by
    intro he
    rw [he,zero_pow (by decide : 4≠0)] at hroot
    exact htheta hroot.symm
  have he := cyclic_phase_weight x y hk theta hcycle
  have htx : theta^(Paper2.weight x)≠0 := pow_ne_zero _ htheta
  have hty : theta^(Paper2.weight y)≠0 := pow_ne_zero _ htheta
  calc
    _ = (b/a)^4 * (theta^(Paper2.weight x)/theta^(Paper2.weight y)) := by
      rw [div_pow,mul_pow,mul_pow,inv_pow,inv_pow,
        ←pow_mul,←pow_mul,Nat.mul_comm (Paper2.weight y) 4,
        Nat.mul_comm (Paper2.weight x) 4,pow_mul,pow_mul,hroot]
      field_simp
      simp only [hroot,one_div,inv_pow,inv_mul_cancel₀ htx]
    _ = 1 := by
      rw [hratio,div_eq_mul_inv,←mul_assoc,he,mul_inv_cancel₀ hty]

end
end Paper2.DegreeCSP.TwoWordContext
