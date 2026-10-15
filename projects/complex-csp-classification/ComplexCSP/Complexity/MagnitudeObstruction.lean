import ComplexCSP.Complexity.ReducedGram
import ComplexCSP.Algebra.ObstructionCommonRepresentation
import ComplexCSP.Complexity.AbsoluteField

/-! # Complete common-field reduction for the magnitude obstruction branch -/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityMagnitudeObstruction
open scoped BigOperators
open ComplexityReducedGram FiniteValueField PlanarHom PlanarHom.Complexity
variable {D : Type} [Fintype D] {s : ℕ}

/-- The common field is constructed from input entries, actual purified entries,
and their magnitudes. The output is a finite nonnegative Gram matrix together
with the complete charged reduction to the original language representation. -/
def witness (L : Language D ℂ (Fin s))
    (hL : ∀ i a,IsAlgebraic ℚ (L.value i a))
    (T : PositiveTable D) (P : Presentation L (Fin (T.rowArity+1)))
    (hP : P.table=T.value) (hr : 0<T.rowArity)
    (hbad : ¬BlockOrthogonality.BlockRankOne (RowTypes.tableRows (LegalSingletonPurification.value T))) :
    Witness L := by
  let Q := LegalSingletonPurification.value T
  let extra : ((Fin (T.rowArity+1) → D) ⊕ (Fin (T.rowArity+1) → D)) → ℂ :=
    Sum.elim Q (fun a => (‖Q a‖ : ℂ))
  have he : ∀ e,IsAlgebraic ℚ (extra e) := by
    intro e
    cases e with
    | inl a => exact LegalSingletonPurification.algebraic T a
    | inr a => exact ComplexityAbsoluteField.norm_algebraic (LegalSingletonPurification.algebraic T a)
  let K := inputField L extra
  let basis := inputBasis L extra hL he
  have hQ : ∀ a,Q a ∈ K := fun a => extra_mem L extra (Sum.inl a)
  let Q0 := ObstructionCommonRepresentation.purified L extra T hQ
  let A0 : (Fin (T.rowArity+1) → D) → K :=
    fun a => ⟨(‖Q a‖ : ℂ),extra_mem L extra (Sum.inr a)⟩
  let A := GramPowerGadget.matrix A0 1 1
  let B : (Fin T.rowArity → D) → D → ℝ := fun x z => ‖Q (Fin.snoc x z)‖
  have hGram : ∀ x y,(A x y : ℂ)=((∑ z,B x z*B y z : ℝ) : ℂ) := by
    intro x y
    change K.subtype _ = _
    change K.subtype (∑ z,A0 (Fin.snoc x z)^1*A0 (Fin.snoc y z)^1) = _
    rw [map_sum,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [map_mul,map_pow,map_pow]
    change (‖Q (Fin.snoc x z)‖ : ℂ)^1*(‖Q (Fin.snoc y z)‖ : ℂ)^1 =
      ((‖Q (Fin.snoc x z)‖*‖Q (Fin.snoc y z)‖ : ℝ) : ℂ)
    simp only [pow_one,Complex.ofReal_mul]
  have hminor : StrictPrincipalMinor (fun x y => (A x y : ℂ)) :=
    strict_minor_of_norm_gram (RowTypes.tableRows Q) hbad A hGram
  have hred : PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem (binaryLanguage A) basis)
      (ComplexityCSPCountReduction.partitionProblem (inputLanguage L extra) basis) :=
    (ComplexityObstructionCompositions.absoluteGramReduction basis Q0 A0 hr K.subtype (fun _ => rfl)).trans
      (ObstructionCommonRepresentation.reduction L extra hL he T P hP hQ)
  exact ofFinite L K (inputFinite L extra hL he) basis (inputLanguage L extra) rfl A B
    (fun _ _ => norm_nonneg _) hGram hminor hred

end ComplexCSP.ComplexityMagnitudeObstruction
