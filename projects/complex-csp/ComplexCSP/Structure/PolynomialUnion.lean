import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-!
# Finite unions of polynomial zero loci

This file proves the mathematical finite-union-to-products construction used in
Corollary 4.4 of the manuscript. It constructs actual multivariate polynomials,
and includes empty equation sets and the empty family of branches.
It does not assume that the manuscript's block-orthogonality certificates have
already been constructed: it supplies the generic algebraic construction to apply
to those certificates once available.
-/

namespace ComplexCSP

open scoped BigOperators

section FiniteProducts

variable {J P : Type*} [Fintype J] [DecidableEq J] [CommMonoid P] [DecidableEq P]

/-- An executable finite enumeration of products of choices, relative to the
supplied multiplication and equality on `P`. -/
def finiteProductFamily (E : J → Finset P) : Finset P :=
  (Fintype.piFinset E).image fun e => ∏ j, e j

theorem mem_finiteProductFamily_iff (E : J → Finset P) (q : P) :
    q ∈ finiteProductFamily E ↔ ∃ e : J → P,
      (∀ j, e j ∈ E j) ∧ (∏ j, e j) = q := by
  simp [finiteProductFamily]

end FiniteProducts

section PolynomialUnion

variable {J σ K : Type*} [Fintype J] [DecidableEq J]
variable [Field K] [DecidableEq K] [DecidableEq σ]

/-- The common zero set of an explicitly finite family of polynomials. -/
def polynomialZeroLocus (E : Finset (MvPolynomial σ K)) : Set (σ → K) :=
  {x | ∀ p ∈ E, MvPolynomial.eval x p = 0}

/-- Enumerate one equation from each branch, multiply, then deduplicate.
An empty branch gives the empty result. No branches gives the singleton `{1}`.
The enumeration is finite, but this semantic specialization is noncomputable
because mathlib's multivariate-polynomial multiplication has no executable code.
`finiteProductFamily` is the executable generic enumeration. -/
noncomputable def productEquations (E : J → Finset (MvPolynomial σ K)) : Finset (MvPolynomial σ K) :=
  finiteProductFamily E

/-- Membership in the finite family of product equations has its concrete
finite-selection meaning. -/
theorem mem_productEquations_iff (E : J → Finset (MvPolynomial σ K))
    (q : MvPolynomial σ K) :
    q ∈ productEquations E ↔ ∃ e : J → MvPolynomial σ K,
      (∀ j, e j ∈ E j) ∧ (∏ j, e j) = q := by
  exact mem_finiteProductFamily_iff E q

/-- Corollary 4.4's algebraic step: membership in a finite union of zero sets is
exactly vanishing of all products choosing one equation from each branch. -/
theorem finite_union_zeroLocus_iff (E : J → Finset (MvPolynomial σ K)) (x : σ → K) :
    (∃ j, x ∈ polynomialZeroLocus (E j)) ↔
      x ∈ polynomialZeroLocus (productEquations E) := by
  classical
  constructor
  · rintro ⟨j, hj⟩ q hq
    obtain ⟨e, he, rfl⟩ := (mem_productEquations_iff E q).mp hq
    rw [MvPolynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ j) (hj (e j) (he j))
  · intro h
    by_contra hn
    have hex : ∀ j, ∃ p ∈ E j, MvPolynomial.eval x p ≠ 0 := by
      intro j
      have hj : ¬ (∀ p ∈ E j, MvPolynomial.eval x p = 0) :=
        fun hz => hn ⟨j, hz⟩
      simpa only [not_forall, exists_prop] using hj
    choose e he hne using hex
    have hp : (∏ j, e j) ∈ productEquations E :=
      (mem_productEquations_iff E _).mpr ⟨e, he, rfl⟩
    have hzero := h _ hp
    rw [MvPolynomial.eval_prod] at hzero
    exact (Finset.prod_ne_zero_iff.mpr fun j _ => hne j) hzero

/-- The same equivalence expressed as equality of sets. -/
theorem zeroLocus_productEquations (E : J → Finset (MvPolynomial σ K)) :
    polynomialZeroLocus (productEquations E) = ⋃ j, polynomialZeroLocus (E j) := by
  ext x
  simp only [Set.mem_iUnion]
  exact (finite_union_zeroLocus_iff E x).symm

/-- If any branch has no equations, the product equation family is empty. -/
theorem productEquations_eq_empty_of_empty_branch
    (E : J → Finset (MvPolynomial σ K)) (j : J) (hj : E j = ∅) :
    productEquations E = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨e, he, _⟩ := (mem_productEquations_iff E q).mp hq
  simpa [hj] using he j

omit [DecidableEq K] [DecidableEq σ] in
/-- An empty equation system imposes no condition. -/
@[simp] theorem polynomialZeroLocus_empty :
    polynomialZeroLocus (∅ : Finset (MvPolynomial σ K)) = Set.univ := by
  ext x
  simp [polynomialZeroLocus]

/-- If there are no branches, the construction yields the equation `1 = 0`,
correctly representing the empty union over a field. -/
theorem productEquations_of_isEmpty [IsEmpty J]
    (E : J → Finset (MvPolynomial σ K)) :
    productEquations E = {1} := by
  ext q
  simp only [mem_productEquations_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact Finset.prod_of_isEmpty _
  · rintro rfl
    exact ⟨isEmptyElim, fun j => isEmptyElim j, Finset.prod_of_isEmpty _⟩

end PolynomialUnion

end ComplexCSP
