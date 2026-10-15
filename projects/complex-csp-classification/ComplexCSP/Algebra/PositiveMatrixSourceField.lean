import ComplexCSP.Instances.MatrixCSPMixedAdapter
import ComplexCSP.Complexity.CSPFieldTransport
import PlanarHom.AlgebraicProductInterpolation

/-! # Exact fixed-field transport of the planar normalization-moment source

The moment source generates its own real coefficient field. It is proved to
embed in the actual supplied real field, and a charged fixed-coordinate descent
transfers its hardness to the real matrix CSP codec.
-/
noncomputable section
open Classical
namespace ComplexCSP.PositiveMatrixSourceField
open PlanarHom PlanarHom.Complexity AlgebraicProductInterpolation
variable (K : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K] {q : ℕ}

def source (A : Matrix (Fin q) (Fin q) K) : RealLanguage q 1 0 where
  matrices _ i j := (A i j : ℝ)
  unaries u := u.elim0
  weights _ := 1
  matrices_algebraic _ i j := (IsIntegral.map K.val (IsIntegral.of_finite (R := ℚ) (A i j))).isAlgebraic
  unaries_algebraic u := u.elim0
  weights_algebraic _ := isAlgebraic_one

theorem field_le (A : Matrix (Fin q) (Fin q) K) : (source K A).field ≤ K := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨i,rfl⟩
  rcases i with ⟨l,i,j⟩ | h
  · exact (A i j).property
  · rcases h with ⟨u,i⟩ | h
    · exact u.elim0
    · rcases h with i | u
      · exact K.one_mem
      · exact u.elim0

def inclusion (A : Matrix (Fin q) (Fin q) K) : (source K A).field →ₐ[ℚ] K :=
  IntermediateField.inclusion (field_le K A)

@[simp] theorem inclusion_matrix (A : Matrix (Fin q) (Fin q) K) (l : Fin 1) (i j : Fin q) :
    inclusion K A ((source K A).matricesK l i j) = A i j := Subtype.ext rfl

@[simp] theorem source_weight (A : Matrix (Fin q) (Fin q) K) (i : Fin q) :
    (source K A).weightsK i = 1 := Subtype.ext rfl

theorem mapped_language (A : Matrix (Fin q) (Fin q) K) :
    (MatrixCSP.language ((source K A).matricesK 0)).mapValues (inclusion K A).toRingHom =
      MatrixCSP.language A := by
  unfold MatrixCSP.language Language.mapValues
  congr 1

theorem source_problem (A : Matrix (Fin q) (Fin q) K) :
    (source K A).problem = MixedCode.evaluationProblem (source K A).basis
      (fun _ : Fin 1 => (source K A).matricesK 0) (fun u : Fin 0 => u.elim0) (fun _ => 1) := by
  have hu : (source K A).unariesK = (fun u : Fin 0 => u.elim0) := funext (fun u => u.elim0)
  unfold RealLanguage.problem
  rw [hu]
  rfl

/-- Actual matrix-code and rational-coordinate machines for the source problem. -/
def toCSP (A : Matrix (Fin q) (Fin q) K) {d : ℕ} (basis : Module.Basis (Fin d) ℚ K) :
    PromisePolyTimeTuringReduction (source K A).problem
      (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) := by
  rw [source_problem]
  have h := ComplexityCSPFieldTransport.descentReduction
    (MatrixCSP.language ((source K A).matricesK 0)) (source K A).basis basis (inclusion K A)
  rw [mapped_language] at h
  exact (MatrixCSPMixedAdapter.reduction (source K A).basis ((source K A).matricesK 0)).trans h

end ComplexCSP.PositiveMatrixSourceField
