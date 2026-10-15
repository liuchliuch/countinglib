import Counting.Algorithm.Pfaffian.Evaluator

/-!
# Executable rational clients

These regressions execute the list evaluator itself. Their equality proofs use
kernel reduction, without a native-evaluation axiom. The final semantic checks
transport computed values to the independent signed pairing sum.
-/

namespace Counting.Algorithm.Pfaffian.Examples

/-- The empty product is one. -/
theorem empty_grid : evaluateGrid ([] : Grid ℚ) = 1 := by decide

/-- A nonzero odd-dimensional input still has no perfect pairing. -/
def oddGrid : Grid ℚ := [[0, 2, -3], [-2, 0, 5], [3, -5, 0]]

theorem odd_grid : evaluateGrid oddGrid = 0 := by decide

/-- The first row has no pivot, although the remaining block is nonzero. -/
def noPivotGrid : Grid ℚ :=
  [[0, 0, 0, 0], [0, 0, 5, 7], [0, -5, 0, 11], [0, -7, -11, 0]]

theorem no_pivot_grid : evaluateGrid noPivotGrid = 0 := by decide

/-- The first candidate vanishes, so the chosen tail position is odd.
The Schur update uses negative entries and a nonintegral intermediate value. -/
def pivotSwapMatrix : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![0, 0, 2, -3], ![0, 0, 5, 7], ![-2, -5, 0, 11], ![3, -7, -11, 0]]

theorem pivot_swap_grid : evaluateGrid (matrixRows pivotSwapMatrix) = -29 := by decide +kernel

/-- All three terms in the four-vertex pairing formula are nonzero. -/
def fourMatrix : Matrix (Fin 4) (Fin 4) ℚ :=
  ![![0, 1, 2, 3], ![-1, 0, 4, 5], ![-2, -4, 0, 6], ![-3, -5, -6, 0]]

theorem four_grid : evaluateGrid (matrixRows fourMatrix) = 8 := by decide +kernel

/-- Missing entries are zero; diagonal and lower-triangle input are normalized. -/
theorem ragged_grid : evaluateGrid ([[99, 3], [7]] : Grid ℚ) = 3 := by decide +kernel

private theorem pivotSwapMatrix_skew : ∀ i j, pivotSwapMatrix j i = -pivotSwapMatrix i j :=
  by decide

private theorem pivotSwapMatrix_diag : ∀ i, pivotSwapMatrix i i = 0 := by decide

private theorem fourMatrix_skew : ∀ i j, fourMatrix j i = -fourMatrix i j := by decide

private theorem fourMatrix_diag : ∀ i, fourMatrix i i = 0 := by decide

/-- Concrete semantic regression through the public basis-indexed bridge. -/
theorem pivot_swap_pairing : pairingPfaffian pivotSwapMatrix = -29 := by
  rw [← evaluateGrid_matrixRows (Module.Basis.singleton (Fin 1) ℚ)
    pivotSwapMatrix pivotSwapMatrix_skew pivotSwapMatrix_diag]
  exact pivot_swap_grid

/-- The computed value is the signed matching expansion, including all pairings. -/
theorem four_pairing : pairingPfaffian fourMatrix = 8 := by
  rw [← evaluateGrid_matrixRows (Module.Basis.singleton (Fin 1) ℚ)
    fourMatrix fourMatrix_skew fourMatrix_diag]
  exact four_grid

/-- The rational specialization keeps the upstream exact number-field codec. -/
theorem rational_fp :
    PfaffianPort.Complexity.FP (gridEncoding (Module.Basis.singleton (Fin 1) ℚ))
      (PfaffianPort.Complexity.numberFieldEncoding (Module.Basis.singleton (Fin 1) ℚ))
      (evaluateGrid (K := ℚ)) :=
  fp_evaluateGrid (Module.Basis.singleton (Fin 1) ℚ)

#eval evaluateGrid ([] : Grid ℚ)
#eval evaluateGrid oddGrid
#eval evaluateGrid noPivotGrid
#eval evaluateGrid (matrixRows pivotSwapMatrix)
#eval evaluateGrid (matrixRows fourMatrix)
#eval evaluateGrid ([[99, 3], [7]] : Grid ℚ)

end Counting.Algorithm.Pfaffian.Examples
