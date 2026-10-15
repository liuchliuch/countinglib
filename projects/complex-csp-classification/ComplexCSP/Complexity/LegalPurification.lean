import ComplexCSP.Complexity.ReplacementField
import ComplexCSP.Algebra.PurificationProductCompatibility

/-! # Actual legal purification is a fixed-language polynomial-time reduction

The finite ambient set and its legal generating choice construct the output
values, their algebraicity, zero preservation, and all product-collision tests.
The common exact field and the bit-costed replacement machine are then derived.
-/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityLegalPurification
open GeneratingSet PlanarHom PlanarHom.Complexity ComplexityCSPCode
variable {D : Type} [Fintype D] {s : ℕ} (L : Language D ℂ (Fin s))
variable {S : Finset ℂˣ} (P : LegalGeneratingSet S)

abbrev Position := (i : Fin s) × (Fin (L.arity i) → D)

def rows (i : Position L) (_ : Unit) : ℂ := L.value i.1 i.2

def Contains : Prop := ∀ i a (hz : L.value i a≠0),Units.mk0 (L.value i a) hz ∈ S

omit [Fintype D] in
theorem contains_rows (h : Contains L (S:=S)) : LegalGeneratingSet.ContainsTable S (rows L) :=
  fun i _ hi => h i.1 i.2 hi

def values (h : Contains L (S:=S)) (i : Fin s) (a : Fin (L.arity i) → D) : ℂ :=
  P.purifyTable (rows L) (contains_rows L h) ⟨i,a⟩ ()

omit [Fintype D] in
theorem values_algebraic (h : Contains L (S:=S)) :
    ∀ i a,IsAlgebraic ℚ (values L P h i a) :=
  fun i a => PurificationProductCompatibility.legal_algebraic P (rows L) (contains_rows L h) ⟨i,a⟩ ()

omit [Fintype D] in
theorem values_zero (h : Contains L (S:=S)) :
    ∀ i a,L.value i a=0 → values L P h i a=0 :=
  fun i a hz => P.purifyTable_zero (rows L) (contains_rows L h) ⟨i,a⟩ () hz

omit [Fintype D] in
theorem entries_compatible (h : Contains L (S:=S)) :
    ProductCompatibility.Compatible (entryValue L)
      (ComplexityCSPReplacement.targetEntry L (values L P h)) := by
  let index : Entry L → Option (Position L × Unit) := fun a => a.map (fun i => (i,()))
  have hc := (PurificationProductCompatibility.legal_compatible_withUnit
    P (rows L) (contains_rows L h)).comp index
  have hs : (fun a => PurificationProductCompatibility.withUnit
      (fun p : Position L × Unit => rows L p.1 p.2) (index a)) = entryValue L := by
    funext a
    cases a <;> rfl
  have ht : (fun a => PurificationProductCompatibility.withUnit
      (fun p : Position L × Unit => P.purifyTable (rows L) (contains_rows L h) p.1 p.2)
      (index a)) = ComplexityCSPReplacement.targetEntry L (values L P h) := by
    funext a
    cases a <;> rfl
  simpa only [Function.comp_def,hs,ht] using hc

/-- The complete fixed-language reduction to the original problem, with actual
field construction, preprocessing, interpolation, and answer-size bounds. -/
def reduction (h : Contains L (S:=S)) (hL : ∀ i a,IsAlgebraic ℚ (L.value i a)) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem
        (ComplexityCSPReplacement.language
          (ComplexityReplacementField.sourceLanguage L (values L P h))
          (ComplexityReplacementField.targetValues L (values L P h)))
        (ComplexityReplacementField.basis L (values L P h) hL (values_algebraic L P h)))
      (ComplexityCSPCountReduction.partitionProblem
        (ComplexityReplacementField.sourceLanguage L (values L P h))
        (ComplexityReplacementField.basis L (values L P h) hL (values_algebraic L P h))) :=
  ComplexityReplacementField.reduction L (values L P h) hL (values_algebraic L P h)
    (entries_compatible L P h) (values_zero L P h)

end ComplexCSP.ComplexityLegalPurification
