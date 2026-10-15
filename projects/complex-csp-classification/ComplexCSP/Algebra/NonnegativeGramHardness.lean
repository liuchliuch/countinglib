import ComplexCSP.Algebra.NonnegativeGramHardnessCore
import PlanarHom.PositivePottsFoundationClosed

/-! # Closed general-graph counting hardness for the actual Gram obstruction

The independent Potts/#P foundation is the source-replayed closed theorem.
There is no hardness, dichotomy, oracle-program, pinning or interpolation
hypothesis. The original paper's false simple-instance Theorem 5.2 is not used.
-/
noncomputable section
open Classical
namespace ComplexCSP.NonnegativeGramHardness
open PlanarHom PlanarHom.Complexity AlgebraicProductInterpolation
open scoped BigOperators
variable {I C : Type} [Fintype I] [Fintype C]
variable (K : IntermediateField ℚ ℝ) {d : ℕ}

/-- The positive symmetric strict-principal-minor case on any finite color set. -/
theorem positive_strict_minor_hard (basis : Module.Basis (Fin d) ℚ K)
    (A : Matrix I I K) (hpos : ∀ i j,0<A i j) (hs : ∀ i j,A i j=A j i)
    (x y : I) (hminor : A x y*A y x < A x x*A y y) :
    PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) :=
  PositiveMatrixHardnessCore.positive_strict_minor_hard_of_potts K basis
    RealLanguage.positivePottsFoundation A hpos hs x y hminor

/-- Actual nonnegative Gram matrices with a strict positive principal minor are
#P-hard on general graphs via the complete charged reduction chain. -/
theorem hard (basis : Module.Basis (Fin d) ℚ K) (A : Matrix I I K)
    (hA : ∀ i j,0≤A i j) (hs : ∀ i j,A i j=A j i)
    (B : I → C → ℝ) (hB : ∀ i z,0≤B i z)
    (hGram : ∀ i j,(A i j : ℝ)=∑ z,B i z*B j z)
    (i j : I) (hm : PositiveGramPowerField.StrictMinor K A i j) :
    PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) :=
  NonnegativeGramHardnessCore.hard_of_potts K basis RealLanguage.positivePottsFoundation
    A hA hs B hB hGram i j hm

end ComplexCSP.NonnegativeGramHardness
