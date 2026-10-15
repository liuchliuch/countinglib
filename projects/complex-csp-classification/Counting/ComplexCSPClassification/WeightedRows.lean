import ComplexCSP.Complexity.RowNormalization
import ComplexCSP.Complexity.MaltsevCacheBounds
import ComplexCSP.Structure.WeightedMaltsevStructure

/-! Fixed-field row algorithms used by weighted Maltsev elimination.

The field, rational basis, and domain size are fixed program parameters. Row
coordinates are runtime input. These are the source's actual bit-cost FP
machines; no classification or uniform-recognition complexity is asserted.
-/
namespace Counting.ComplexCSP.Classification.WeightedRows

open PlanarHom PlanarHom.Complexity
open ComplexCSP.ComplexityRowNormalization

variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K]
variable {dimension d : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

theorem normalize_inFP :
    FP (rowEncoding basis d) (resultEncoding basis d) normalize :=
  fp_normalize basis

omit [DecidableEq K] in
theorem sum_inFP :
    FP (rowEncoding basis d) (numberFieldEncoding basis) rowSum :=
  fp_rowSum basis

omit [Algebra ℚ K] in
theorem normalize_exact (v : Row K d) : normalize v = none ↔ v = 0 :=
  normalize_none_iff v

end Counting.ComplexCSP.Classification.WeightedRows
