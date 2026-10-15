import Mathlib.Analysis.CStarAlgebra.Matrix
open scoped Matrix.Norms.Operator
example {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (inferInstance : TopologicalSpace (Matrix ι ι ℝ)) =
    (Matrix.linftyOpNormedAddCommGroup (m := ι) (n := ι) (α := ℝ)).toUniformSpace.toTopologicalSpace := by
  rfl
