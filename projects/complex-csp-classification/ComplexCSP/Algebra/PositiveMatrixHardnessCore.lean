import ComplexCSP.Algebra.PositiveMatrixMomentBridge
import ComplexCSP.Complexity.CSPColorRelabeling

/-! # Positive-matrix hardness on arbitrary finite color types

The finite-color reindexing has an actual charged identity-query reduction.
The Potts foundation parameter is discharged in the final closed wrapper.
-/
noncomputable section
open Classical
namespace ComplexCSP.PositiveMatrixHardnessCore
open PlanarHom PlanarHom.Complexity AlgebraicProductInterpolation
variable {D : Type} [Fintype D] (K : IntermediateField ℚ ℝ) {d : ℕ}

theorem positive_strict_minor_hard_of_potts (basis : Module.Basis (Fin d) ℚ K)
    (hPotts : RealLanguage.PositivePottsFoundation) (A : Matrix D D K)
    (hpos : ∀ i j,0<A i j) (hs : ∀ i j,A i j=A j i)
    (x y : D) (hminor : A x y*A y x < A x x*A y y) :
    PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) := by
  letI : FiniteDimensional ℚ K := Module.Finite.of_basis basis
  let e : Fin (Fintype.card D) ≃ D := (Fintype.equivFin D).symm
  letI : Nonempty (Fin (Fintype.card D)) := ⟨e.symm x⟩
  let N : Matrix (Fin (Fintype.card D)) (Fin (Fintype.card D)) K := fun i j => A (e i) (e j)
  have hh := PositiveMatrixMomentBridge.positive_strict_minor_hard_of_potts K basis hPotts N
    (fun i j => hpos (e i) (e j)) (fun i j => hs (e i) (e j)) (e.symm x) (e.symm y)
    (by simpa only [N,e.apply_symm_apply] using hminor)
  exact hh.trans (ComplexityCSPColorRelabeling.reduction (MatrixCSP.language A) e basis)

end ComplexCSP.PositiveMatrixHardnessCore
