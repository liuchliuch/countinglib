/- Source-adapted generic algebra; provenance: docs/UNIFORM_BOUND_REUSE.json. -/
import Paper2.HeightOne.GroupSplit.PGL
import Paper2.HeightOne.UniformBound.Quantitative.TraceValues
import Paper2.HeightOne.UniformBound.Quantitative.FiniteTrace
import Paper2.HeightOne.UniformBound.Quantitative.ProjectiveClasses

/-! A computable degree-only bound for the actual finite projective subgroup.
This strengthens the quantitative API of source Lemma 5.2 without adding an
order, trace, or cardinality premise. It is supporting work for subsequent
finite group-growth arguments, not a new numbered source result. -/

namespace Paper2.HeightOne.GroupSplit
open Paper2.HeightOne.GroupSplit.MatrixGroup

/-- A coarse uniform bound depending only on the number-field degree. -/
def uniformProjectiveBound (D : ℕ) : ℕ := (2 * torsionExponent D) ^ 4

theorem uniformProjectiveBound_pos (D : ℕ) : 0 < uniformProjectiveBound D := by
  exact pow_pos (Nat.mul_pos (by decide) (torsionExponent_pos D)) 4

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {L : Type*} [Field L] [NumberField L]

/-- A multiplicatively closed projectively torsion set of nonsingular matrices
over a number field has uniformly boundedly many literal projective classes. -/
theorem ncard_projective_image_le_uniformBound {G : Set (Binary (K := L))}
    (hdet : ∀ T ∈ G, Matrix.det T ≠ 0)
    (hmul : ∀ T ∈ G, ∀ U ∈ G, T * U ∈ G)
    (htorsion : ∀ T ∈ G, ProjectivelyFinite T) :
    (projectiveClass '' G).ncard ≤ uniformProjectiveBound (Module.finrank ℚ L) := by
  let E := AlgebraicClosure L
  let f := algebraMap L E
  let S := determinantOneLifts f G
  have hmulS : ∀ U ∈ S, ∀ V ∈ S, U * V ∈ S :=
    fun U hU V hV => determinantOneLifts_mul_mem f hmul hU hV
  have htorsionS : ∀ U ∈ S, IsOfFinOrder U :=
    fun U hU => determinantOneLifts_isOfFinOrder f htorsion hU
  have htrace : (Matrix.trace '' S).Finite :=
    finite_trace_image_of_lifts hdet htorsion (fun U hU => hU)
  have hS : S.Finite := finite_matrix_set_of_finite_traces hmulS htorsionS htrace
  have htraceCard : (Matrix.trace '' S).ncard ≤
      2 * torsionExponent (Module.finrank ℚ L) :=
    ncard_trace_image_of_lifts_le hdet htorsion (fun U hU => hU)
  calc
    (projectiveClass '' G).ncard ≤ S.ncard := by
      apply ncard_projective_image_le_of_lifts f hS
      · intro T hT hz
        exact hdet T hT (by rw [hz, Matrix.det_zero])
      · intro T hT
        obtain ⟨c, hc, hU⟩ := exists_mem_determinantOneLifts f hT (hdet T hT)
        exact ⟨c • T.map f, hU, c, hc, rfl⟩
    _ ≤ (Matrix.trace '' S).ncard ^ 4 :=
      ncard_matrix_set_le_trace_image_pow_four hmulS htorsionS htrace
    _ ≤ uniformProjectiveBound (Module.finrank ℚ L) :=
      Nat.pow_le_pow_left htraceCard 4

/-- Uniform cardinal bound for the genuine subgroup represented by `G`. -/
theorem card_projectiveSubgroup_le_uniformBound {G : Set (Binary (K := L))}
    (hG : ProjectiveMatrixGroup G)
    (htorsion : ∀ T ∈ G, ProjectivelyFinite T) :
    Nat.card (projectiveSubgroup hG) ≤ uniformProjectiveBound (Module.finrank ℚ L) := by
  rw [card_projectiveSubgroup_eq hG]
  exact ncard_projective_image_le_uniformBound (fun T hT => hG.det_ne_zero hT)
    hG.mul_mem htorsion


end
end Paper2.HeightOne.GroupSplit
