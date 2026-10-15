import ComplexCSP.Recognition.CertificatesFiniteLocus
import ComplexCSP.Algebra.NumberFieldTorsion

/-!
# The actual finite number-field root alphabet

The alphabet is the subgroup of roots killed by the proved field exponent.
It contains every finite-order field element. Its inverse lookup realizes
complex conjugation under every field embedding into the complex numbers.
Its mathematical `Fintype` is noncomputable; effective root enumeration in a
chosen exact number-field representation remains separate.
-/

namespace ComplexCSP.Certificates

open RowDetector

variable (K : Type*) [Field K] [NumberField K]

instance fieldExponent_neZero : NeZero (fieldExponent K) := ⟨ne_of_gt (fieldExponent_pos K)⟩

noncomputable abbrev NumberFieldRoots := rootsOfUnity (fieldExponent K) K

noncomputable instance numberFieldRootsFintype : Fintype (NumberFieldRoots K) :=
  Fintype.ofFinite _

noncomputable def numberFieldRootAlphabet : RootAlphabet K (NumberFieldRoots K) where
  value := fun r ↦ (r.val : K)
  one := 1
  conj := Inv.inv
  value_one := rfl

variable {K}

@[simp] theorem numberFieldRoot_value (r : NumberFieldRoots K) :
    (numberFieldRootAlphabet K).value r = (r.val : K) := rfl

theorem numberFieldRoot_ne_zero (r : NumberFieldRoots K) :
    (numberFieldRootAlphabet K).value r ≠ 0 := Units.ne_zero r.val

theorem numberFieldRoot_finite_order (r : NumberFieldRoots K) :
    IsOfFinOrder ((numberFieldRootAlphabet K).value r) := by
  apply isOfFinOrder_iff_pow_eq_one.mpr
  exact ⟨fieldExponent K, fieldExponent_pos K, (mem_rootsOfUnity' _ _).mp r.property⟩

/-- Every field root of unity is an entry of the actual finite alphabet. -/
theorem numberFieldRoots_complete (a : K) (ha : IsOfFinOrder a) :
    ∃ r : NumberFieldRoots K, (numberFieldRootAlphabet K).value r = a := by
  refine ⟨⟨ha.unit, ?_⟩, rfl⟩
  apply (mem_rootsOfUnity' _ _).mpr
  exact fieldExponent_killsTorsion K a ha

/-- The root alphabet has its genuine complex realization under a field
embedding; conjugation is exactly the inverse lookup. -/
noncomputable def numberFieldRootRealization (φ : K →+* ℂ) :
    ComplexRealization (numberFieldRootAlphabet K) where
  hom := φ
  norm_root r := (φ.toMonoidHom.isOfFinOrder (numberFieldRoot_finite_order r)).norm_eq_one
  conj_root r := by
    change φ (((r⁻¹ : NumberFieldRoots K).val : K)) = star (φ (r.val : K))
    simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
    rw [map_inv₀, Complex.inv_def, Complex.normSq_eq_norm_sq]
    have hn : ‖φ (r.val : K)‖ = 1 :=
      (φ.toMonoidHom.isOfFinOrder (numberFieldRoot_finite_order r)).norm_eq_one
    simp [hn]

end ComplexCSP.Certificates
