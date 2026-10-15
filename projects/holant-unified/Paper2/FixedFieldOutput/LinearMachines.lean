import Paper2.FixedFieldOutput.Problem
import Paper2.Complexity.BellMachines.FieldArithmetic
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Actual fixed-rational-matrix machines between chosen finite field outputs.
The constants are fixed before graph input. A linear retraction only specifies
those constants; the running program executes finite rational arithmetic. -/
namespace Paper2.FixedFieldOutput
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines Paper2.Algebraic
open Paper2.ExactInput Paper2.Problem Paper2.Tractable
open scoped BigOperators
noncomputable section

def matrixComputes {m n : ℕ} (A : Fin n → Fin m → ℚ) :
    Computes (vectorEncoding m) (vectorEncoding n)
      (fun v j => ∑ i, v i * A j i) :=
  assembleComputes (vectorEncoding m) n _ (fun j =>
    BellMachines.rationalProvider.sumComputes (vectorEncoding m) m
      (fun v i => v i * A j i) (fun i =>
        BellMachines.rationalProvider.mulComputes (coordinateComputes m i)
          (constantComputes (vectorEncoding m) rationalEncoding (A j i))))

def linearComputes {m n : ℕ} (A : (Fin m → ℚ) →ₗ[ℚ] (Fin n → ℚ)) :
    Computes (vectorEncoding m) (vectorEncoding n) A := by
  apply congrComputes (matrixComputes (fun j i => A (Pi.single i 1) j))
  intro v
  have hv : v = ∑ i : Fin m, v i • Pi.single i (1 : ℚ) := by
    ext j
    simp [Finset.sum_apply,Pi.single_apply]
  conv_rhs => rw [hv]
  ext j
  simp [map_sum,Finset.sum_apply]

/-- A fixed linear projection onto the target coefficient field. This is not
an executable algebraic-input decoder; only finitely many projected basis
vectors occur as rational constants in `conversionComputes`. -/
def projection (L : Language) : AlgebraicComplex →ₗ[ℚ] L.coefficientField :=
  L.coefficientField.val.toLinearMap.leftInverse

 theorem projection_embed (L : Language) (x : L.coefficientField) :
    projection L (x : AlgebraicComplex) = x := by
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr (fun x y h => Subtype.ext h)

def conversion (source target : Language) : Answer source →ₗ[ℚ] Answer target :=
  target.fieldPresentation.basis.equivFun.toLinearMap.comp
    ((projection target).comp (source.coefficientField.val.toLinearMap.comp
      source.fieldPresentation.decode.toLinearMap))

def conversionComputes (source target : Language) :
    Computes (answerEncoding source) (answerEncoding target) (conversion source target) :=
  linearComputes (conversion source target)

 theorem conversion_correct (source target : Language) (v : Answer source) (u : Answer target)
    (h : (source.fieldPresentation.decode v : AlgebraicComplex) =
      (target.fieldPresentation.decode u : AlgebraicComplex)) :
    conversion source target v = u := by
  change target.fieldPresentation.basis.equivFun
    (projection target (source.fieldPresentation.decode v : AlgebraicComplex)) = u
  rw [h,projection_embed]
  exact target.fieldPresentation.basis.equivFun.apply_symm_apply u

 theorem conversion_answer (ws wt : Wiring) (source target : Language)
    (G : Instance source) (H : Instance target)
    (h : value ws source G = value wt target H) :
    conversion source target (answer ws source G) = answer wt target H :=
  conversion_correct source target _ _
    ((answer_correct ws source G).trans (h.trans (answer_correct wt target H).symm))

end
end Paper2.FixedFieldOutput
