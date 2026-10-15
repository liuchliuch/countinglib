import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Fintype.Pi

/-! Exact multiaffine generating polynomials for finite Boolean tensors.
Every original tensor coefficient is retained as one square-free monomial. -/
namespace Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection.Polynomial
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {ι : Type} [Fintype ι]

def exponent (x : ι → Bool) : ι →₀ ℕ := by
  classical
  exact Finsupp.onFinset Finset.univ (fun i => if x i then 1 else 0)
    (fun i _ => Finset.mem_univ i)

@[simp] theorem exponent_apply (x : ι → Bool) (i : ι) :
    exponent x i=if x i then 1 else 0 := by
  classical
  simp [exponent]

theorem exponent_injective : Function.Injective (exponent (ι:=ι)) := by
  intro x y eqn
  funext i
  have h := congrArg (fun d : ι →₀ ℕ => d i) eqn
  simp only [exponent_apply] at h
  cases hx : x i <;> cases hy : y i <;> simp_all

variable {K : Type} [CommSemiring K]

def encode (f : (ι → Bool) → K) : MvPolynomial ι K := by
  classical
  exact ∑ x : ι → Bool,MvPolynomial.monomial (exponent x) (f x)

def decode (p : MvPolynomial ι K) (x : ι → Bool) : K := p.coeff (exponent x)

@[simp] theorem encode_coeff_word (f : (ι → Bool) → K) (x : ι → Bool) :
    (encode f).coeff (exponent x)=f x := by
  classical
  simp only [encode,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial,
    exponent_injective.eq_iff]
  simp

theorem encode_coeff_outside (f : (ι → Bool) → K) (d : ι →₀ ℕ)
    (outside : ¬∃ x : ι → Bool,exponent x=d) : (encode f).coeff d=0 := by
  classical
  simp only [encode,MvPolynomial.coeff_sum,MvPolynomial.coeff_monomial]
  apply Finset.sum_eq_zero
  intro x _
  exact ite_eq_right (fun eqn => outside ⟨x,eqn⟩)

theorem encode_injective : Function.Injective (encode (ι:=ι) (K:=K)) := by
  intro f g equal
  funext x
  have h := congrArg (fun p : MvPolynomial ι K => p.coeff (exponent x)) equal
  simpa only [encode_coeff_word] using h

@[simp] theorem decode_encode (f : (ι → Bool) → K) : decode (encode f)=f := by
  funext x
  exact encode_coeff_word f x

theorem multiaffine_encode (f : (ι → Bool) → K) :
    ∀ i,MvPolynomial.degreeOf i (encode f)≤1 := by
  intro i
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d member
  have live : (encode f).coeff d≠0 := MvPolynomial.mem_support_iff.mp member
  obtain ⟨x,rfl⟩ : ∃ x : ι → Bool,exponent x=d := by
    by_contra none
    exact live (encode_coeff_outside f d none)
  simp only [exponent_apply]
  cases x i <;> simp

/-- Every multiaffine polynomial has precisely the Boolean tensor given by
its square-free coefficients, including constant and zero polynomials. -/
theorem encode_decode (p : MvPolynomial ι K)
    (degree : ∀ i,MvPolynomial.degreeOf i p≤1) : encode (decode p)=p := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases small : ∀ i,d i≤1
  · let x : ι → Bool := fun i => decide (d i=1)
    have ex : exponent x=d := by
      ext i
      rw [exponent_apply]
      dsimp only [x]
      by_cases one : d i=1
      · simp [one]
      · have zero : d i=0 := by have h:=small i;omega
        simp [zero]
    rw [←ex,encode_coeff_word]
    rfl
  · have noWord : ¬∃ x : ι → Bool,exponent x=d := by
      rintro ⟨x,rfl⟩
      apply small
      intro i
      rw [exponent_apply]
      cases x i <;> simp
    rw [encode_coeff_outside _ _ noWord]
    symm
    by_contra live
    have member : d∈p.support := MvPolynomial.mem_support_iff.mpr live
    apply small
    intro i
    exact le_trans (MvPolynomial.le_degreeOf_of_mem_support i member) (degree i)

theorem encode_eq_zero_iff (f : (ι → Bool) → K) : encode f=0 ↔ f=0 := by
  constructor
  · intro zero
    funext x
    have h := congrArg (fun p : MvPolynomial ι K => p.coeff (exponent x)) zero
    simpa only [encode_coeff_word,AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply,Pi.zero_apply] using h
  · intro zero
    subst f
    simp [encode]

/-- Evaluating a tensor generating polynomial gives the literal product of
one-port covectors `[1,z_i]`, with no omitted assignments. -/
theorem eval_encode [DecidableEq ι] (f : (ι → Bool) → K) (z : ι → K) :
    MvPolynomial.eval z (encode f)=
      ∑ x : ι → Bool,f x*(∏ i,z i^(if x i then 1 else 0)) := by
  classical
  simp only [encode,MvPolynomial.eval_sum,MvPolynomial.eval_monomial]
  apply Finset.sum_congr (by ext x; simp)
  intro x _
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [exponent_apply]


theorem exponent_equiv {κ : Type} [Fintype κ] (e : ι ≃ κ) (x : ι → Bool) :
    (exponent x).mapDomain e=exponent (fun j => x (e.symm j)) := by
  classical
  ext j
  rw [Finsupp.mapDomain_equiv_apply,exponent_apply,exponent_apply]

/-- Renaming ports is the exact renaming of polynomial variables. -/
theorem encode_reindex {κ : Type} [Fintype κ] (e : ι ≃ κ)
    (f : (ι → Bool) → K) :
    encode (fun x : κ → Bool => f (fun i => x (e i)))=MvPolynomial.rename e (encode f) := by
  classical
  let E : (ι → Bool) ≃ (κ → Bool) := {
    toFun x j := x (e.symm j)
    invFun y i := y (e i)
    left_inv x := by funext i;simp
    right_inv y := by funext j;simp }
  simp only [encode,map_sum,MvPolynomial.rename_monomial]
  rw [←E.sum_comp]
  apply Finset.sum_congr rfl
  intro x _
  simp only [E,Equiv.coe_fn_mk,e.symm_apply_apply]
  rw [exponent_equiv]

/-- Disjoint tensor products are literal products of the two generating
polynomials, with the same original coefficient multiplication. -/
theorem encode_tensor_product {κ : Type} [Fintype κ]
    (f : (ι → Bool) → K) (g : (κ → Bool) → K) :
    encode (fun x : (ι ⊕ κ) → Bool => f (fun i => x (.inl i))*g (fun j => x (.inr j)))=
      MvPolynomial.rename Sum.inl (encode f)*MvPolynomial.rename Sum.inr (encode g) := by
  classical
  let E := Equiv.sumPiEquivProdPi (fun _ : ι ⊕ κ => Bool)
  have ex (x : ι → Bool) (y : κ → Bool) :
      exponent (Sum.elim x y)=
        (exponent x).mapDomain Sum.inl+(exponent y).mapDomain Sum.inr := by
    rw [←Finsupp.sumElim_eq_add]
    ext z
    cases z <;> simp [exponent_apply]
  simp only [encode,map_sum,Finset.sum_mul,Finset.mul_sum,MvPolynomial.rename_monomial,
    MvPolynomial.monomial_mul_monomial]
  conv_rhs => rw [Finset.sum_comm]
  trans ∑ xy : (ι → Bool) × (κ → Bool),
    MvPolynomial.monomial (exponent (Sum.elim xy.1 xy.2)) (f xy.1*g xy.2)
  · apply Finset.sum_equiv E (by intro x; simp)
    intro z _
    change MvPolynomial.monomial (exponent z)
      (f (fun i => z (.inl i))*g (fun j => z (.inr j)))=
      MvPolynomial.monomial (exponent (Sum.elim (fun i => z (.inl i))
        (fun j => z (.inr j))))
        (f (fun i => z (.inl i))*g (fun j => z (.inr j)))
    have join : Sum.elim (fun i => z (.inl i)) (fun j => z (.inr j))=z := by
      funext i
      cases i <;> rfl
    rw [join]
  · rw [Fintype.sum_prod_type]
    apply Finset.sum_congr (by ext x; simp)
    intro x _
    apply Finset.sum_congr (by ext y; simp)
    intro y _
    rw [ex]

end
end Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection.Polynomial

