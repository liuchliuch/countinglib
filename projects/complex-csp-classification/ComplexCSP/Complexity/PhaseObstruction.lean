import ComplexCSP.Complexity.MagnitudeObstruction
import ComplexCSP.Structure.PhaseLegalObstruction

/-! # Complete common-field reduction for the phase obstruction branch -/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityPhaseObstruction
open scoped BigOperators
open ComplexityReducedGram FiniteValueField PlanarHom PlanarHom.Complexity
variable {D : Type} [Fintype D] {s : ℕ}

def witness (L : Language D ℂ (Fin s))
    (hL : ∀ i a,IsAlgebraic ℚ (L.value i a))
    (T : PositiveTable D) (P : Presentation L (Fin (T.rowArity+1)))
    (hP : P.table=T.value) (hr : 0<T.rowArity) (p q : ℕ)
    (hbad : ¬BlockOrthogonality.BlockRankOne
      (GramPowerGadget.matrix (LegalSingletonPurification.value T) p q)) : Witness L := by
  let R := Fin T.rowArity → D
  let Q := LegalSingletonPurification.value T
  let M := GramPowerGadget.matrix Q p q
  have hMalg : ∀ x y,IsAlgebraic ℚ (M x y) := by
    intro x y
    apply IsIntegral.isAlgebraic
    apply IsIntegral.sum
    intro z _
    exact ((LegalSingletonPurification.algebraic T (Fin.snoc x z)).isIntegral.pow p).mul
      ((LegalSingletonPurification.algebraic T (Fin.snoc y z)).isIntegral.pow q)
  let extra : ((Fin (T.rowArity+1) → D) ⊕ (Fin 2 → R)) → ℂ :=
    Sum.elim Q (fun a => (‖M (a 0) (a 1)‖ : ℂ))
  have he : ∀ e,IsAlgebraic ℚ (extra e) := by
    intro e
    cases e with
    | inl a => exact LegalSingletonPurification.algebraic T a
    | inr a => exact ComplexityAbsoluteField.norm_algebraic (hMalg (a 0) (a 1))
  let K := inputField L extra
  let basis := inputBasis L extra hL he
  have hQ : ∀ a,Q a ∈ K := fun a => extra_mem L extra (Sum.inl a)
  let Q0 := ObstructionCommonRepresentation.purified L extra T hQ
  let A0 : (Fin 2 → R) → K :=
    fun a => ⟨(‖M (a 0) (a 1)‖ : ℂ),extra_mem L extra (Sum.inr a)⟩
  have hMcoe (x y : R) : ((GramPowerGadget.matrix Q0 p q x y : K) : ℂ)=M x y := by
    change K.subtype (∑ z,Q0 (Fin.snoc x z)^p*Q0 (Fin.snoc y z)^q) =
      ∑ z,Q (Fin.snoc x z)^p*Q (Fin.snoc y z)^q
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [map_mul,map_pow,map_pow]
    rfl
  let A := GramPowerGadget.matrix A0 1 1
  let H : (Fin 1 → R) → R → ℂ := fun x z => M (x 0) z
  let B : (Fin 1 → R) → R → ℝ := fun x z => ‖H x z‖
  have hH : ¬BlockOrthogonality.BlockRankOne H := by
    intro hh
    apply hbad
    intro x y hx hy
    exact hh (fun _ => x) (fun _ => y) hx hy
  have hGram : ∀ x y,(A x y : ℂ)=((∑ z,B x z*B y z : ℝ) : ℂ) := by
    intro x y
    change K.subtype (∑ z,A0 (Fin.snoc x z)^1*A0 (Fin.snoc y z)^1) = _
    rw [map_sum,Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro z _
    rw [map_mul,map_pow,map_pow]
    change (‖M (x 0) z‖ : ℂ)^1*(‖M (y 0) z‖ : ℂ)^1 = ((‖M (x 0) z‖*‖M (y 0) z‖ : ℝ) : ℂ)
    simp only [pow_one,Complex.ofReal_mul]
  have hminor : StrictPrincipalMinor (fun x y => (A x y : ℂ)) :=
    strict_minor_of_norm_gram H hH A hGram
  have hred : PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem (binaryLanguage A) basis)
      (ComplexityCSPCountReduction.partitionProblem (inputLanguage L extra) basis) :=
    (ComplexityObstructionCompositions.phaseGramReduction basis Q0 p q hr A0 K.subtype
      (fun a => congrArg (fun z : ℂ => (‖z‖ : ℂ)) (hMcoe (a 0) (a 1)).symm)).trans
      (ObstructionCommonRepresentation.reduction L extra hL he T P hP hQ)
  exact ofFinite L K (inputFinite L extra hL he) basis (inputLanguage L extra) rfl A B
    (fun _ _ => norm_nonneg _) hGram hminor hred

end ComplexCSP.ComplexityPhaseObstruction
