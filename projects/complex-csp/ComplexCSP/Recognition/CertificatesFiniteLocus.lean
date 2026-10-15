import ComplexCSP.Recognition.CertificatesCompleteness
import ComplexCSP.Structure.PolynomialUnion

/-!
# Finite certificate locus and its product equations

This connects the constructed finite branches to actual polynomial zero loci
and to the product-equation construction. The exact finite branch checker is
executable when field/root equality and the finite input types are supplied.
-/

namespace ComplexCSP.Certificates

open scoped BigOperators

variable {X D R K : Type*} [Fintype X] [DecidableEq X]
variable [Fintype D] [DecidableEq D] [Fintype R] [Field K] [DecidableEq K]

/-- The finite equation set of a literal certificate branch. This uses the
semantic polynomial representation, whose multiplication is noncomputable in
mathlib; `equationValue` supplies executable evaluation of the syntax. -/
noncomputable def equationSet (roots : RootAlphabet K R) (c : Certificate X D R) :
    Finset (MvPolynomial (X × D) K) := by
  classical
  exact Finset.univ.image (equation roots c)

omit [Fintype R] in
theorem satisfies_iff_zeroLocus (roots : RootAlphabet K R) (c : Certificate X D R)
    (A : X → D → K) :
    Satisfies roots c A ↔ (fun p : X × D ↦ A p.1 p.2) ∈
      ComplexCSP.polynomialZeroLocus (equationSet roots c) := by
  classical
  simp only [ComplexCSP.polynomialZeroLocus, Set.mem_ofPred_eq, equationSet,
    Finset.forall_mem_image, Finset.mem_univ, forall_true_left, Satisfies]

/-- The retained certificate family as a finite index type. -/
abbrev RetainedCertificate (roots : RootAlphabet K R) :=
  {c : Certificate X D R // c ∈ Certificate.retainedBranches roots}

/-- The literal finite union of branch varieties, at an original field-valued
point and the purified table related to it by intrinsic entry tests. -/
theorem blockOrthogonal_iff_finite_union (roots : RootAlphabet K R)
    (realize : ComplexRealization roots) (A : X → D → K) (P : X → D → ℂ)
    (tests : IntrinsicTests roots realize A P) :
    BlockOrthogonality.BlockOrthogonal P ↔
      ∃ c : RetainedCertificate (X := X) (D := D) roots,
        (fun p : X × D ↦ A p.1 p.2) ∈ ComplexCSP.polynomialZeroLocus (equationSet roots c.val) := by
  rw [blockOrthogonal_iff_certificate tests]
  constructor
  · rintro ⟨c, hc, hA⟩
    refine ⟨⟨c, ?_⟩, (satisfies_iff_zeroLocus roots c A).mp hA⟩
    simp only [Certificate.retainedBranches, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hc
  · rintro ⟨c, hc⟩
    refine ⟨c.val, ?_, (satisfies_iff_zeroLocus roots c.val A).mpr hc⟩
    exact (Finset.mem_filter.mp c.property).2

/-- Actual product polynomials, selecting one equation from every retained
branch, as in Corollary 4.4. -/
noncomputable def boProductEquations (roots : RootAlphabet K R) :
    Finset (MvPolynomial (X × D) K) := by
  classical
  exact ComplexCSP.productEquations
    (fun c : RetainedCertificate (X := X) (D := D) roots ↦ equationSet roots c.val)

/-- Corollary 4.4 specialized to the genuinely constructed finite BO branches,
with the local intrinsic-entry bridge made explicit. -/
theorem blockOrthogonal_iff_product_equations (roots : RootAlphabet K R)
    (realize : ComplexRealization roots) (A : X → D → K) (P : X → D → ℂ)
    (tests : IntrinsicTests roots realize A P) :
    BlockOrthogonality.BlockOrthogonal P ↔
      ∀ q ∈ boProductEquations (X := X) (D := D) roots,
        MvPolynomial.eval (fun p : X × D ↦ A p.1 p.2) q = 0 := by
  classical
  rw [blockOrthogonal_iff_finite_union roots realize A P tests]
  exact ComplexCSP.finite_union_zeroLocus_iff
    (fun c : RetainedCertificate (X := X) (D := D) roots ↦ equationSet roots c.val) _

/-- Exact finite checking of the polynomial equations by executable syntax
rather than mathlib's noncomputable semantic polynomial arithmetic. -/
def checkCertificate (roots : RootAlphabet K R) (c : Certificate X D R)
    (A : X → D → K) : Bool := decide (∀ i, equationValue roots c A i = 0)

omit [DecidableEq X] [Fintype R] in
theorem checkCertificate_correct (roots : RootAlphabet K R) (c : Certificate X D R)
    (A : X → D → K) : checkCertificate roots c A = true ↔ Satisfies roots c A := by
  simp only [checkCertificate, decide_eq_true_eq, satisfies_iff_equationValues]

/-- An executable bounded enumeration of all retained finite certificates. -/
def checkBOByCertificates (roots : RootAlphabet K R) (A : X → D → K) : Bool :=
  decide (∃ c : Certificate X D R, c.Retained roots ∧
    checkCertificate roots c A = true)

/-- Soundness and completeness of the finite branch checker, relative to actual
local intrinsic purification tests. -/
theorem checkBOByCertificates_correct (roots : RootAlphabet K R)
    (realize : ComplexRealization roots) (A : X → D → K) (P : X → D → ℂ)
    (tests : IntrinsicTests roots realize A P) :
    checkBOByCertificates roots A = true ↔ BlockOrthogonality.BlockOrthogonal P := by
  rw [blockOrthogonal_iff_certificate tests]
  simp only [checkBOByCertificates, decide_eq_true_eq, checkCertificate_correct]

end ComplexCSP.Certificates
