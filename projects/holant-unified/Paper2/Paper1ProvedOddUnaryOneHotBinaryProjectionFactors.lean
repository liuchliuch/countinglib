import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionPencil
import Mathlib.Algebra.GCDMonoid.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-! Algebraic factor separation behind higher-arity binary projection.
A singular two-by-two polynomial matrix factors over a GCD domain itself,
and factors of a multiaffine product cannot share any variable. -/
namespace Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection
open Holant
noncomputable section

section Domain
variable {R : Type} [CommRing R] [IsDomain R] [GCDMonoid R]

/-- Rank-one factors stay in the polynomial domain, rather than only its
fraction field. All zero-row and zero-column cases are covered. -/
theorem singular_domain_factors (M : Bool → Bool → R)
    (singular : M false false*M true true-M false true*M true false=0) :
    ∃ u v : Bool → R,∀ i j,M i j=u i*v j := by
  by_cases h00 : M false false=0
  · by_cases h01 : M false true=0
    · refine ⟨(fun i => if i then 1 else 0),(fun j => M true j),?_⟩
      intro i j
      cases i <;> cases j <;> simp [h00,h01]
    · have h10 : M true false=0 := by
        have product : M false true*M true false=0 := by
          simpa only [h00,zero_mul,zero_sub,neg_eq_zero] using singular
        exact (mul_eq_zero.mp product).resolve_left h01
      refine ⟨(fun i => M i true),(fun j => if j then 1 else 0),?_⟩
      intro i j
      cases i <;> cases j <;> simp [h00,h10]
  · obtain ⟨x,y,eq0,eq1,unit⟩ := extract_gcd (M false false) (M false true)
    let g := gcd (M false false) (M false true)
    have gnz : g≠0 := by
      intro zero
      apply h00
      rw [eq0]
      change g*x=0
      rw [zero,zero_mul]
    have xnz : x≠0 := by
      intro zero
      apply h00
      rw [eq0,zero,mul_zero]
    have coprime : IsRelPrime x y := gcd_isUnit_iff_isRelPrime.mp unit
    have cross : x*M true true=y*M true false := by
      apply mul_left_cancel₀ gnz
      change gcd (M false false) (M false true)*(x*M true true)=
        gcd (M false false) (M false true)*(y*M true false)
      rw [←mul_assoc,←eq0,←mul_assoc,←eq1]
      exact sub_eq_zero.mp singular
    have divides : x∣M true false :=
      coprime.dvd_of_dvd_mul_left ⟨M true true,cross.symm⟩
    obtain ⟨h,eq2⟩ := divides
    have eq3 : M true true=y*h := by
      apply mul_left_cancel₀ xnz
      rw [cross,eq2]
      ring
    refine ⟨(fun i => if i then h else g),(fun j => if j then y else x),?_⟩
    intro i j
    cases i <;> cases j <;> simp only [Bool.false_eq_true,ite_false,ite_true]
    · exact eq0
    · exact eq1
    · rw [eq2,mul_comm]
    · rw [eq3,mul_comm]
end Domain

section Multiaffine
variable {K : Type} [CommSemiring K] [NoZeroDivisors K]
variable {σ : Type}

private theorem degreeOf_mul_formula (p q : MvPolynomial σ K) (i : σ)
    (pnz : p≠0) (qnz : q≠0) :
    MvPolynomial.degreeOf i (p*q)=MvPolynomial.degreeOf i p+MvPolynomial.degreeOf i q := by
  classical
  simp_rw [MvPolynomial.degreeOf_eq_natDegree,map_mul,←MvPolynomial.renameEquiv_apply]
  rw [Polynomial.natDegree_mul] <;>
    simpa [-MvPolynomial.renameEquiv_apply,EmbeddingLike.map_eq_zero_iff]

/-- Every variable belongs to at most one nonzero factor of a product
whose degree in each variable is at most one. -/
theorem multiaffine_factor_separation (p q : MvPolynomial σ K)
    (pnz : p≠0) (qnz : q≠0)
    (multiaffine : ∀ i,MvPolynomial.degreeOf i (p*q)≤1) :
    ∀ i,MvPolynomial.degreeOf i p=0 ∨ MvPolynomial.degreeOf i q=0 := by
  intro i
  have bound := multiaffine i
  rw [degreeOf_mul_formula p q i pnz qnz] at bound
  omega

theorem multiaffine_factors (p q : MvPolynomial σ K)
    (pnz : p≠0) (qnz : q≠0)
    (multiaffine : ∀ i,MvPolynomial.degreeOf i (p*q)≤1) :
    (∀ i,MvPolynomial.degreeOf i p≤1) ∧ (∀ i,MvPolynomial.degreeOf i q≤1) := by
  constructor <;> intro i
  all_goals
    have bound := multiaffine i
    rw [degreeOf_mul_formula p q i pnz qnz] at bound
    omega
end Multiaffine

section PolynomialFactors
variable {K : Type} [Field K] {σ : Type}
open MvPolynomial

/-- The conditional matrix factors over the original coefficient field's
polynomial ring. No fraction-field coefficients are introduced. -/
theorem singular_polynomial_matrix_factors (M : Bool → Bool → MvPolynomial σ K)
    (singular : M false false*M true true-M false true*M true false=0) :
    ∃ u v : Bool → MvPolynomial σ K,∀ i j,M i j=u i*v j := by
  let _ := UniqueFactorizationMonoid.toGCDMonoid (MvPolynomial σ K)
  exact singular_domain_factors M singular

/-- Reassemble two distinguished variables from their four conditional
coefficient polynomials. -/
def twoPortPolynomial (M : Bool → Bool → MvPolynomial σ K) :
    MvPolynomial (Bool ⊕ σ) K :=
  rename Sum.inr (M false false)
  +X (.inl false)*rename Sum.inr (M true false)
  +X (.inl true)*rename Sum.inr (M false true)
  +X (.inl false)*X (.inl true)*rename Sum.inr (M true true)

def rowPolynomial (u : Bool → MvPolynomial σ K) : MvPolynomial (Bool ⊕ σ) K :=
  rename Sum.inr (u false)+X (.inl false)*rename Sum.inr (u true)

def columnPolynomial (v : Bool → MvPolynomial σ K) : MvPolynomial (Bool ⊕ σ) K :=
  rename Sum.inr (v false)+X (.inl true)*rename Sum.inr (v true)

theorem twoPort_row_column_factorization
    (M : Bool → Bool → MvPolynomial σ K) (u v : Bool → MvPolynomial σ K)
    (factor : ∀ i j,M i j=u i*v j) :
    twoPortPolynomial M=rowPolynomial u*columnPolynomial v := by
  simp only [twoPortPolynomial,rowPolynomial,columnPolynomial,factor,map_mul]
  ring

private theorem distinguished_not_mem_rename (p : MvPolynomial σ K) (b : Bool) :
    Sum.inl b ∉ (rename Sum.inr p : MvPolynomial (Bool ⊕ σ) K).vars := by
  intro member
  obtain ⟨i,_,eq⟩ := mem_vars_rename Sum.inr p member
  cases eq

theorem rowPolynomial_absent_true (u : Bool → MvPolynomial σ K) :
    Sum.inl true ∉ (rowPolynomial u).vars := by
  classical
  intro member
  have bound := vars_add_subset
    (rename Sum.inr (u false) : MvPolynomial (Bool ⊕ σ) K)
    (X (.inl false)*rename Sum.inr (u true))
  rcases Finset.mem_union.mp (bound member) with h | h
  · exact distinguished_not_mem_rename (u false) true h
  · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
    · simp only [vars_X,Finset.mem_singleton,Sum.inl.injEq] at h
      cases h
    · exact distinguished_not_mem_rename (u true) true h

theorem columnPolynomial_absent_false (v : Bool → MvPolynomial σ K) :
    Sum.inl false ∉ (columnPolynomial v).vars := by
  classical
  intro member
  have bound := vars_add_subset
    (rename Sum.inr (v false) : MvPolynomial (Bool ⊕ σ) K)
    (X (.inl true)*rename Sum.inr (v true))
  rcases Finset.mem_union.mp (bound member) with h | h
  · exact distinguished_not_mem_rename (v false) false h
  · rcases Finset.mem_union.mp (vars_mul _ _ h) with h | h
    · simp only [vars_X,Finset.mem_singleton,Sum.inl.injEq] at h
      cases h
    · exact distinguished_not_mem_rename (v true) false h

/-- Disjoint degree supports yield an actual partition of variables, with
specified ports on opposite sides. Constant factors are allowed; the two
specified ports still make both port blocks nonempty. -/
theorem partition_polynomial_factors (p q : MvPolynomial σ K)
    (pnz : p≠0) (qnz : q≠0)
    (multiaffine : ∀ i,degreeOf i (p*q)≤1)
    (i₀ i₁ : σ) (distinct : i₀≠i₁)
    (absentP : i₁∉p.vars) (absentQ : i₀∉q.vars) :
    ∃ s : Set σ,i₀∈s ∧ i₁∉s ∧
      ∃ a : MvPolynomial s K,∃ b : MvPolynomial ↥(sᶜ) K,
        rename Subtype.val a=p ∧ rename Subtype.val b=q ∧
        (∀ i,degreeOf i a≤1) ∧ (∀ i,degreeOf i b≤1) := by
  classical
  let s : Set σ := (p.vars : Set σ) ∪ {i₀}
  have h₀ : i₀∈s := Or.inr rfl
  have h₁ : i₁∉s := by
    rintro (member | eq)
    · exact absentP member
    · exact distinct eq.symm
  have pbound : (p.vars : Set σ) ⊆ Set.range ((↑) : s → σ) := by
    intro i member
    exact ⟨⟨i,Or.inl member⟩,rfl⟩
  have qbound : (q.vars : Set σ) ⊆ Set.range ((↑) : ↥(sᶜ) → σ) := by
    intro i member
    have outside : i∉s := by
      rintro (pmember | eq)
      · have degrees := multiaffine_factor_separation p q pnz qnz multiaffine i
        rcases degrees with degree | degree
        · exact (mem_vars_iff_degreeOf_ne_zero.mp pmember) degree
        · exact (mem_vars_iff_degreeOf_ne_zero.mp member) degree
      · exact absentQ (eq ▸ member)
    exact ⟨⟨i,outside⟩,rfl⟩
  obtain ⟨a,aeq⟩ := exists_rename_eq_of_vars_subset_range p Subtype.val
    Subtype.val_injective pbound
  obtain ⟨b,beq⟩ := exists_rename_eq_of_vars_subset_range q Subtype.val
    Subtype.val_injective qbound
  have degrees := multiaffine_factors p q pnz qnz multiaffine
  refine ⟨s,h₀,h₁,a,b,aeq,beq,?_,?_⟩
  · intro i
    have bound := degrees.1 i.val
    rw [←aeq,degreeOf_rename_of_injective Subtype.val_injective] at bound
    exact bound
  · intro i
    have bound := degrees.2 i.val
    rw [←beq,degreeOf_rename_of_injective Subtype.val_injective] at bound
    exact bound

/-- A determinant identity for the conditional two-port matrix gives
polynomial factors on two disjoint, nonempty port blocks. -/
theorem singular_twoPort_partition (M : Bool → Bool → MvPolynomial σ K)
    (singular : M false false*M true true-M false true*M true false=0)
    (nonzero : twoPortPolynomial M≠0)
    (multiaffine : ∀ i,degreeOf i (twoPortPolynomial M)≤1) :
    ∃ s : Set (Bool ⊕ σ),Sum.inl false∈s ∧ Sum.inl true∉s ∧
      ∃ a : MvPolynomial s K,∃ b : MvPolynomial ↥(sᶜ) K,
        twoPortPolynomial M=rename Subtype.val a*rename Subtype.val b ∧
        (∀ i,degreeOf i a≤1) ∧ (∀ i,degreeOf i b≤1) := by
  obtain ⟨u,v,factor⟩ := singular_polynomial_matrix_factors M singular
  have equation := twoPort_row_column_factorization M u v factor
  have pnz : rowPolynomial u≠0 := by
    intro zero
    apply nonzero
    rw [equation,zero,zero_mul]
  have qnz : columnPolynomial v≠0 := by
    intro zero
    apply nonzero
    rw [equation,zero,mul_zero]
  have bounds : ∀ i,degreeOf i (rowPolynomial u*columnPolynomial v)≤1 := by
    intro i
    rw [←equation]
    exact multiaffine i
  obtain ⟨s,h₀,h₁,a,b,aeq,beq,da,db⟩ := partition_polynomial_factors
    (rowPolynomial u) (columnPolynomial v) pnz qnz bounds
    (.inl false) (.inl true) (by intro eq; cases eq)
    (rowPolynomial_absent_true u) (columnPolynomial_absent_false v)
  exact ⟨s,h₀,h₁,a,b,by rw [aeq,beq,equation],da,db⟩
end PolynomialFactors

end
end Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection

