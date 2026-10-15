import ComplexCSP.Algebra.EncodedNumberFieldElement
import Mathlib.Algebra.Algebra.Equiv

/-! # The coordinate field's own power basis

These are semantic structures on the executable element carrier. The basis
coordinates are exactly the stored rational vector; no classical coordinate
extraction is called by runtime field arithmetic or enumeration.
-/
set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP.EncodedNumberField.Element
variable {n : ℕ} {c : CoeffVector n} [Fact (Valid n c)]

/-- Runtime generator coordinates, correct also in degree one. -/
def generator : Element n c := ⟨shift c (EncodedNumberField.one n)⟩

omit [Fact (Valid n c)] in
@[simp] theorem Model.value_generator (M : Model n c) : M.value (Element.generator (c := c)) = M.generator := by
  change interpret M.generator (shift c (EncodedNumberField.one n)) = _
  rw [interpret_shift _ _ _ M.relation,
    interpret_one M.generator (show 0 < n from M.powerBasis.dim_pos), mul_one]

/-- A proof-level isomorphism to any genuine semantic model of the same data. -/
noncomputable def Model.valueRingEquiv (M : Model n c) : Element n c ≃+* M.K where
  toFun := M.value
  invFun z := ⟨M.powerBasis.basis.equivFun z⟩
  left_inv a := by
    apply Element.ext
    exact coordinates_interpret M.powerBasis a.coeff
  right_inv z := interpret_coordinates M.powerBasis z
  map_add' := M.value_add
  map_mul' := M.value_mul

omit [Fact (Valid n c)] in
@[simp] theorem Model.valueRingEquiv_apply (M : Model n c) (a : Element n c) :
    M.valueRingEquiv a = M.value a := rfl

/-- The model isomorphism respects the rational algebra structures. -/
noncomputable def Model.valueAlgEquiv (M : Model n c) : Element n c ≃ₐ[ℚ] M.K :=
  AlgEquiv.ofRingEquiv (f := M.valueRingEquiv) (by
    intro q
    simp)

/-- The indicated basis has exactly the stored coefficient map. -/
noncomputable def powerBasis : PowerBasis ℚ (Element n c) where
  gen := generator
  dim := n
  basis := Module.Basis.ofEquivFun coeffLinearEquiv
  basis_eq_pow := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    intro i
    apply M.value_injective
    rw [M.value_pow, M.value_generator]
    have hb : ((Module.Basis.ofEquivFun (coeffLinearEquiv (n := n) (c := c))) i).coeff =
        unitVector i := by
      simp only [Module.Basis.coe_ofEquivFun]
      change Pi.single i 1 = unitVector i
      funext j
      simp [unitVector, Pi.single_apply, eq_comm]
    change interpret M.generator _ = _
    rw [hb, interpret_unitVector]

@[simp] theorem powerBasis_dim : (powerBasis (n := n) (c := c)).dim = n := rfl
@[simp] theorem powerBasis_gen : (powerBasis (n := n) (c := c)).gen = generator := rfl

@[simp] theorem powerBasis_coordinates (a : Element n c) :
    (powerBasis (n := n) (c := c)).basis.equivFun a = a.coeff := by
  change (Module.Basis.ofEquivFun (coeffLinearEquiv (n := n) (c := c))).equivFun a = a.coeff
  rw [Module.Basis.equivFun_ofEquivFun]
  rfl

/-- Evaluation at the own-field generator is literally the wrapped input vector. -/
@[simp] theorem interpret_generator (a : CoeffVector n) :
    interpret (generator (n := n) (c := c)) a = (⟨a⟩ : Element n c) := by
  have h := interpret_coordinates (powerBasis (n := n) (c := c)) (⟨a⟩ : Element n c)
  rw [powerBasis_gen, powerBasis_coordinates] at h
  exact h

/-- The runtime reduction equation holds in the own-field power basis. -/
theorem generator_relation : (generator (n := n) (c := c)) ^ n = interpret generator c := by
  obtain ⟨M⟩ := (Fact.out : Valid n c)
  apply M.value_injective
  rw [M.value_pow, M.value_generator, interpret_generator]
  exact M.relation

end ComplexCSP.EncodedNumberField.Element
