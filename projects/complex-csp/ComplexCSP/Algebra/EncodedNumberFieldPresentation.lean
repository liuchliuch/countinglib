import ComplexCSP.Algebra.EncodedNumberFieldPowerBasis
import ComplexCSP.Algebra.UniformCyclotomicExtensionValidation
import ComplexCSP.Algebra.EffectiveRootsRuntimeAlphabet

/-! # The checked coordinate field has its own integral presentation

The presentation is proof-only. Its power basis is the own-field basis with
exactly the stored coordinates, making the runtime root enumeration directly
usable on Element rather than on a chosen abstract model.
-/
namespace ComplexCSP.EncodedNumberField.Element
open Polynomial
variable {n : ℕ} {c : CoeffVector n} [Fact (Valid n c)]

/-- The coordinate field itself is a genuine semantic model of the runtime data. -/
noncomputable def selfModel : Model n c where
  K := Element n c
  field := inferInstance
  algebra := inferInstance
  generator := Element.generator
  basis := powerBasis.basis
  basis_eq_pow := powerBasis.basis_eq_pow
  relation := generator_relation

variable (a : Fin n → ℤ) [Fact (Valid n (EffectiveRoots.coefficientRelation a))]

/-- The checked tail's integer polynomial annihilates the actual runtime generator. -/
theorem checkedTail_integer_root :
    aeval (generator (c := EffectiveRoots.coefficientRelation a))
      (MonicIrreducibility.denote (MonicIrreducibility.fromTail a)) = 0 :=
  AlgebraicEncoding.model_integer_polynomial_root a
    (selfModel (c := EffectiveRoots.coefficientRelation a))

/-- A successful raw guard provides the root enumerator's genuine integral
presentation certificate on Element itself. No enumeration result is assumed. -/
theorem integralPresentation_of_checkedTail
    (ha : MonicIrreducibility.irreducibleMonicTail a = true) :
    EffectiveRoots.IntegralPresentation n a (generator (c := EffectiveRoots.coefficientRelation a)) := by
  let p := MonicIrreducibility.denote (MonicIrreducibility.fromTail a)
  have hp : p.Monic := MonicIrreducibility.denote_monic _
    (MonicIrreducibility.fromTail_leading a)
  have hi : Irreducible (p.map (Int.castRingHom ℚ)) :=
    (MonicIrreducibility.irreducibleMonicTail_correct a).mp ha
  refine ⟨powerBasis.basis, powerBasis.basis_eq_pow, p, hp, checkedTail_integer_root a, ?_, ?_⟩
  · apply minpoly.eq_of_irreducible_of_monic hi _ (hp.map _)
    change aeval (generator (c := EffectiveRoots.coefficientRelation a))
      (p.map (algebraMap ℤ ℚ)) = 0
    rw [aeval_map_algebraMap]
    exact checkedTail_integer_root a
  · intro i
    simp [p, MonicIrreducibility.coefficient, MonicIrreducibility.fromTail,
      i.isLt, show i.val < n + 1 by omega]

end ComplexCSP.EncodedNumberField.Element
