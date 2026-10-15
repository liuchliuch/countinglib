import Paper2.Problem
import Paper2.ExactInput.FixedFamilyField

/-! A single number field is derived from the original literal finite family.
The field and rational structure constants are fixed before the graph is read.
This supplies exact semantic coordinates; public minimal-root output conversion
is handled by separate codec modules. -/
namespace Paper2.ExactInput
open Paper2.Tractable Paper2.Algebraic Paper2.Problem
open scoped BigOperators

namespace Language

abbrev CoefficientIndex (L : Language) := Σ i : Fin L.count, Fin (2 ^ L.arity i.val)

noncomputable def coefficient (L : Language) (a : L.CoefficientIndex) : AlgebraicComplex :=
  L.signature a.1 ((wordIndex (L.arity a.1.val)).symm a.2)

noncomputable def coefficientField (L : Language) := familyField L.coefficient

theorem coefficient_algebraic (L : Language) (a : L.CoefficientIndex) :
    IsAlgebraic ℚ (L.coefficient a) := Algebra.IsAlgebraic.isAlgebraic _

instance coefficientField_finiteDimensional (L : Language) :
    FiniteDimensional ℚ L.coefficientField :=
  familyField_finiteDimensional L.coefficient (L.coefficient_algebraic)

noncomputable def fieldPresentation (L : Language) :
    FixedField L.coefficientField (Module.finrank ℚ L.coefficientField) :=
  familyPresentation L.coefficient (L.coefficient_algebraic)

/-- Every original value embeds without rescaling in this same fixed field. -/
theorem signature_mem_field (L : Language) (i : Fin L.count) (x : Fin (L.arity i.val) → Bool) :
    L.signature i x ∈ L.coefficientField := by
  have h := coefficient_mem_familyField L.coefficient ⟨i, wordIndex (L.arity i.val) x⟩
  simpa [coefficientField, coefficient] using h

noncomputable def fieldSignature (L : Language) (i : Fin L.count) :
    Signature L.coefficientField (L.arity i.val) :=
  fun x => ⟨L.signature i x, L.signature_mem_field i x⟩

@[simp] theorem fieldSignature_coe (L : Language) (i : Fin L.count)
    (x : Fin (L.arity i.val) → Bool) : (L.fieldSignature i x : AlgebraicComplex) = L.signature i x := rfl

end Language

noncomputable def fieldKernel (L : Language) : Wiring → Kernel L.coefficientField
  | .ordinary => Signature.equality
  | .nativeX => Signature.disequality

@[simp] theorem fieldKernel_coe (L : Language) (w : Wiring) (a b : Bool) :
    (fieldKernel L w a b : AlgebraicComplex) = w.kernel a b := by
  cases w <;> cases a <;> cases b <;> rfl

noncomputable def fieldNetwork (w : Wiring) (L : Language) (G : Instance L) :
    Network L.coefficientField 0 :=
  G.val.realize G.property L.fieldSignature (fun _ => fieldKernel L w)

/-- Evaluation in the derived fixed field is literally the original tensor sum. -/
theorem fieldNetwork_value (w : Wiring) (L : Language) (G : Instance L) :
    ((fieldNetwork w L G).denote Fin.elim0 : AlgebraicComplex) = value w L G := by
  change L.coefficientField.subtype ((fieldNetwork w L G).denote Fin.elim0) = _
  simp only [Network.denote, map_sum, map_mul, map_prod]
  apply Finset.sum_congr rfl
  intro z _
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  exact fieldKernel_coe L w _ _

/-- Rational coordinates are fixed-field output, not yet public root descriptors. -/
noncomputable def outputCoordinates (w : Wiring) (L : Language) (G : Instance L) :
    Fin (Module.finrank ℚ L.coefficientField) → ℚ :=
  L.fieldPresentation.basis.equivFun ((fieldNetwork w L G).denote Fin.elim0)

theorem outputCoordinates_spec (w : Wiring) (L : Language) (G : Instance L) :
    (L.fieldPresentation.decode (outputCoordinates w L G) : AlgebraicComplex) = value w L G := by
  change ((L.fieldPresentation.basis.equivFun.symm
    (L.fieldPresentation.basis.equivFun _)) : AlgebraicComplex) = _
  rw [LinearEquiv.symm_apply_apply]
  exact fieldNetwork_value w L G

/-- Public strict descriptors exist for the actual fixed-field coordinate output.
This is coverage only; it asserts no effective algorithm or polynomial bound. -/
theorem public_output_exists (w : Wiring) (L : Language) (G : Instance L) :
    ∃ c : RootCode, c.MinimalRepresents (value w L G : ℂ) := RootCode.minimal_coverage _

end Paper2.ExactInput
