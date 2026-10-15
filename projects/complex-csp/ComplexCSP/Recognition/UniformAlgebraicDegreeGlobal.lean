import ComplexCSP.Recognition.UniformAlgebraicGlobal
import ComplexCSP.Algebra.EncodedNumberFieldDegreeGlobal

/-! # Exact recognition: degree recognition from separate algebraic input

Both the initial common field and the cyclotomic extension are computed by proved
terminating finite-data searches. The runtime has no complex values, field-model
witnesses, primitive-root oracle, or supplied equality-comparison table.
-/
namespace ComplexCSP.Recognition
open AlgebraicEncoding EncodedNumberField

variable {D ι : Type} [Fintype D] [DecidableEq D] [Encodable D]
variable [Fintype ι] [Encodable ι]

/-- Exact uniform degree-multiple algorithm for valid algebraic descriptions. -/
def uniformAlgebraicDegreeGlobalTest (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) (δ : ℕ) (hδ : 0 < δ) : Bool :=
  let input := algebraicDescriptions L
  let C := findInitialInputCandidate input (algebraicDescriptions_valid L hL)
  let hv := InitialInputCandidate.test_valid
    (findInitialInputCandidate_spec input (algebraicDescriptions_valid L hL))
  coordinateDegreeGlobalTest C.tail hv δ hδ (candidateLanguage L C)

/-- Correctness refers to the exact original complex input language and all
actual degree-multiple instances, not to the searched extension's unrelated data. -/
theorem uniformAlgebraicDegreeGlobalTest_correct_jointBO [Nonempty D]
    (L : Language D AlgebraicInput ι) (hL : ValidAlgebraicLanguage L)
    (δ : ℕ) (hδ : 0 < δ)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a)) :
    uniformAlgebraicDegreeGlobalTest L hL δ hδ = true ↔
      DegreeJointBO (realizedAlgebraicLanguage L z) δ := by
  let input := algebraicDescriptions L
  let hvInput := algebraicDescriptions_valid L hL
  let C := findInitialInputCandidate input hvInput
  let hv := InitialInputCandidate.test_valid (findInitialInputCandidate_spec input hvInput)
  letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
    ⟨validTail_sound C.tail hv⟩
  let values : Fin (Fintype.card (AlgebraicEntryIndex L)) → ℂ := fun k =>
    let x := (algebraicEntryNumbering L).symm k
    z x.1 x.2
  have hvalues (k) : (input k).Represents (values k) := hz _ _
  obtain ⟨σ,hσ,_⟩ := findInitialInputCandidate_sound input hvInput values hvalues
  have he : (candidateLanguage L C).mapValues σ = realizedAlgebraicLanguage L z := by
    have hh : (fun i a => σ (C.coordinateValue (algebraicEntryNumbering L ⟨i,a⟩))) = z := by
      funext i a
      have hs := hσ (algebraicEntryNumbering L ⟨i,a⟩)
      change σ (C.coordinateValue (algebraicEntryNumbering L ⟨i,a⟩)) =
        (fun x : AlgebraicEntryIndex L => z x.1 x.2)
          ((algebraicEntryNumbering L).symm (algebraicEntryNumbering L ⟨i,a⟩)) at hs
      rw [Equiv.symm_apply_apply] at hs
      exact hs
    change Language.mk L.arity L.arity_pos
      (fun i a => σ (C.coordinateValue (algebraicEntryNumbering L ⟨i,a⟩))) =
        Language.mk L.arity L.arity_pos z
    rw [hh]
  have hc := coordinateDegreeGlobalTest_correct C.tail hv δ hδ (candidateLanguage L C) σ
  rwa [he] at hc

/-- All three degree-multiple structural conditions are recognized uniformly. -/
theorem uniformAlgebraicDegreeGlobalTest_correct_conditions [Nonempty D]
    (L : Language D AlgebraicInput ι) (hL : ValidAlgebraicLanguage L)
    (δ : ℕ) (hδ : 0 < δ)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a)) :
    uniformAlgebraicDegreeGlobalTest L hL δ hδ = true ↔
      DegreeCaiChenConditions (realizedAlgebraicLanguage L z) δ :=
  (uniformAlgebraicDegreeGlobalTest_correct_jointBO L hL δ hδ z hz).trans
    (degree_structural_collapse (realizedAlgebraicLanguage L z) δ
      (fun i a => (hz i a).isAlgebraic)).symm

end ComplexCSP.Recognition
