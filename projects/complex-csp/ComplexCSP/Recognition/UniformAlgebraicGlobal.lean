import ComplexCSP.Algebra.InitialInputSearch
import ComplexCSP.Algebra.EncodedNumberFieldGlobal
import ComplexCSP.Algebra.AlgebraicInputCompleteness

/-! # Exact recognition: uniform recognition from separate algebraic descriptions

Every table entry is an integer coefficient list and rational isolating rectangle.
The program converts these descriptions to a checked common number field and
runs the exact global certificate algorithm. Complex values, field models,
primitive presentations, root lists and identity oracles are absent from the
runtime arguments. Validity proofs for standard algebraic descriptions are erased.
-/
namespace ComplexCSP.Recognition
open AlgebraicEncoding EncodedNumberField

variable {D ι : Type} [Fintype D] [DecidableEq D] [Encodable D]
variable [Fintype ι] [Encodable ι]

abbrev AlgebraicEntryIndex (L : Language D AlgebraicInput ι) := Σ i, Fin (L.arity i) → D

def algebraicEntryNumbering (L : Language D AlgebraicInput ι) :
    AlgebraicEntryIndex L ≃ Fin (Fintype.card (AlgebraicEntryIndex L)) :=
  Encodable.fintypeEquivFin

/-- The actual finite entry descriptions, in a computable canonical order. -/
def algebraicDescriptions (L : Language D AlgebraicInput ι) :
    Fin (Fintype.card (AlgebraicEntryIndex L)) → AlgebraicInput := fun k =>
  let x := (algebraicEntryNumbering L).symm k
  L.value x.1 x.2

/-- Validity is precisely the individual standard encoding promise. -/
def ValidAlgebraicLanguage (L : Language D AlgebraicInput ι) : Prop :=
  ∀ i a, (L.value i a).Valid

omit [DecidableEq D] in
 theorem algebraicDescriptions_valid (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) : ∀ k, (algebraicDescriptions L k).Valid := by
  intro k
  exact hL _ _

/-- The semantic language using the input's exact shape. -/
def realizedAlgebraicLanguage (L : Language D AlgebraicInput ι)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ) : Language D ℂ ι :=
  ⟨L.arity,L.arity_pos,z⟩

/-- The searched common-field coordinates in the input's original signature shape. -/
def candidateLanguage (L : Language D AlgebraicInput ι)
    (C : InitialInputCandidate (Fintype.card (AlgebraicEntryIndex L))) :
    Language D C.FieldType ι :=
  ⟨L.arity,L.arity_pos,fun i a => C.coordinateValue (algebraicEntryNumbering L ⟨i,a⟩)⟩

/-- Full uniform finite-data algorithm, total for valid algebraic input encodings. -/
def uniformAlgebraicGlobalTest (L : Language D AlgebraicInput ι)
    (hL : ValidAlgebraicLanguage L) : Bool :=
  let input := algebraicDescriptions L
  let C := findInitialInputCandidate input (algebraicDescriptions_valid L hL)
  let hv := InitialInputCandidate.test_valid
    (findInitialInputCandidate_spec input (algebraicDescriptions_valid L hL))
  coordinateGlobalTest C.tail hv (candidateLanguage L C)

/-- The full arbitrary-algebraic-input algorithm accepts exactly the actual
joint BO condition of the represented language, with unbounded instances. -/
theorem uniformAlgebraicGlobalTest_correct_jointBO [Nonempty D]
    (L : Language D AlgebraicInput ι) (hL : ValidAlgebraicLanguage L)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a)) :
    uniformAlgebraicGlobalTest L hL = true ↔ JointBO (realizedAlgebraicLanguage L z) := by
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
  have hc := coordinateGlobalTest_correct C.tail hv (candidateLanguage L C) σ
  rwa [he] at hc

/-- Uniform recognition of all three source structural conditions. This theorem
uses the separately proved all-instance repair, not the false original 5.2. -/
theorem uniformAlgebraicGlobalTest_correct_conditions [Nonempty D]
    (L : Language D AlgebraicInput ι) (hL : ValidAlgebraicLanguage L)
    (z : ∀ i, (Fin (L.arity i) → D) → ℂ)
    (hz : ∀ i a, (L.value i a).Represents (z i a)) :
    uniformAlgebraicGlobalTest L hL = true ↔ CaiChenConditions (realizedAlgebraicLanguage L z) :=
  (uniformAlgebraicGlobalTest_correct_jointBO L hL z hz).trans
    (structural_collapse (realizedAlgebraicLanguage L z) (fun i a => (hz i a).isAlgebraic)).symm

omit [Fintype D] [DecidableEq D] [Encodable D] [Fintype ι] [Encodable ι] in
/-- Every finite algebraic complex language has a finite input description for
this very algorithm, with exactly the same domain, arities and selected values. -/
theorem exists_algebraic_language_description (L : Language D ℂ ι)
    (hL : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    ∃ (E : Language D AlgebraicInput ι)
      (z : ∀ i, (Fin (E.arity i) → D) → ℂ),
      (∀ i a, (E.value i a).Represents (z i a)) ∧ realizedAlgebraicLanguage E z = L := by
  classical
  choose input hinput using fun i a => exists_algebraicInput_represents (L.value i a) (hL i a)
  exact ⟨⟨L.arity,L.arity_pos,input⟩,L.value,hinput,rfl⟩

end ComplexCSP.Recognition
