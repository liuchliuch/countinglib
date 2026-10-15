import ComplexCSP.Algebra.PositiveMatrixSourceField
import ComplexCSP.Instances.ConditionedNormalizedClasses
import ComplexCSP.Instances.ConditionedMatrixReduction
import PlanarHom.PositiveNormalizationMomentConsequences

/-! # Arbitrary-color positive hardness from actual normalization moments

This module isolates the one external proved foundation parameter so its
source-only replay may finish independently. The closed wrapper supplies the
actual PositivePottsFoundationClosed theorem, never an assumed dichotomy.
-/
noncomputable section
open Classical
namespace ComplexCSP.PositiveMatrixMomentBridge
open PlanarHom PlanarHom.Complexity AlgebraicProductInterpolation
open ConditionedRowMoments
open scoped BigOperators

/-- A quotient weight is literally the sum over all original class members. -/
theorem quotientWeight_class {R : Type} [Fintype R] (A : R → R → ℝ)
    (hpos : ∀ i j,0<A i j) (hs : ∀ i j,A i j=A j i) (w : R → ℝ) (x : R) :
    Twins.quotientWeight (diagonalNormalize A) w (Quotient.mk _ x) = classWeight A w x := by
  have he (i : R) : Quotient.mk (Twins.rowSetoid (diagonalNormalize A)) i = Quotient.mk _ x ↔
      normalized A i = normalized A x :=
    ⟨fun h => funext (Quotient.exact h),fun h => Quotient.sound (congrFun h)⟩
  rw [←normalizedClassWeight_eq A hpos hs]
  unfold Twins.quotientWeight
  rw [←Finset.sum_subtype (Finset.univ.filter (fun i : R =>
    Quotient.mk (Twins.rowSetoid (diagonalNormalize A)) i = Quotient.mk _ x)) (by simp) w]
  simp only [Finset.sum_filter,he,normalizedClassWeight]

variable (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K] {q d : ℕ}
variable [Nonempty (Fin q)]

/-- Non-hardness of the actual encoded matrix problem forces the precise
normalized-class first-moment invariant, including every twin multiplicity. -/
theorem balanced_of_not_hard (basis : Module.Basis (Fin d) ℚ K)
    (hPotts : RealLanguage.PositivePottsFoundation) (A : Matrix (Fin q) (Fin q) K)
    (hpos : ∀ i j,0<A i j) (hs : ∀ i j,A i j=A j i)
    (hnot : ¬ PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis)) :
    Balanced (fun i j => (A i j : ℝ)) := by
  let L := PositiveMatrixSourceField.source K A
  have hnotL : ¬ PromisedSharpPHard L.problem := fun h => hnot (h.trans (PositiveMatrixSourceField.toCSP K A basis))
  have hsR : ∀ i j,(A i j : ℝ)=(A j i : ℝ) := fun i j => congrArg Subtype.val (hs i j)
  intro x y
  have h := L.normalized_moments_constant hPotts 0 hsR hpos (fun _ => rfl) hnotL 1
    (Quotient.mk _ x) (Quotient.mk _ y)
  simp only [pow_one] at h
  exact (quotientWeight_class (fun i j => (A i j : ℝ)) hpos hsR _ x).symm.trans
    (h.trans (quotientWeight_class (fun i j => (A i j : ℝ)) hpos hsR _ y))

/-- A strict positive principal minor makes at least one genuinely available
conditioned source violate the required first-moment invariant. -/
theorem positive_strict_minor_hard_of_potts (basis : Module.Basis (Fin d) ℚ K)
    (hPotts : RealLanguage.PositivePottsFoundation) (A : Matrix (Fin q) (Fin q) K)
    (hpos : ∀ i j,0<A i j) (hs : ∀ i j,A i j=A j i)
    (x y : Fin q) (hminor : A x y * A y x < A x x * A y y) :
    PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) := by
  letI : IsStrictOrderedRing K := Subfield.toIsStrictOrderedRing K.toSubfield
  by_contra hnot
  have hsR : ∀ i j,(A i j : ℝ)=(A j i : ℝ) := fun i j => congrArg Subtype.val (hs i j)
  have hmR : (A x y : ℝ)^2 < (A x x : ℝ)*(A y y : ℝ) := by
    change (A x y : ℝ)*(A y x : ℝ)<(A x x : ℝ)*(A y y : ℝ) at hminor
    simpa only [hsR y x,pow_two] using hminor
  apply not_both_balanced (fun i j => (A i j : ℝ)) hpos hsR x y hmR
  have hbal (z : Fin q) : Balanced (condition (fun i j => (A i j : ℝ)) z) := by
    let N := ConditionedMatrixCode.conditioned A z
    have hnpos : ∀ i j,0<N i j := fun i j => mul_pos (mul_pos (hpos i j) (hpos i z)) (hpos j z)
    have hns : ∀ i j,N i j=N j i := by
      intro i j
      dsimp [N,ConditionedMatrixCode.conditioned]
      rw [hs j i]
      ring
    have hnnot : ¬ PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language N) basis) :=
      fun h => hnot (h.trans (ConditionedMatrixCode.reduction basis A z))
    exact balanced_of_not_hard K basis hPotts N hnpos hns hnnot
  exact ⟨hbal x,hbal y⟩

end ComplexCSP.PositiveMatrixMomentBridge
