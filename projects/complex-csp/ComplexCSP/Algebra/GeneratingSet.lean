import ComplexCSP.Algebra.OriginalPurification

/-!
# Constructing exponent coordinates modulo torsion

For every finitely generated abelian group the torsion-free quotient is a
finite free integer module. We choose a finite basis and lift its quotient map
using projectivity. This constructs the exponent map and a splitting; neither
map is postulated. Its kernel is proved to be exactly the finite-order elements.
-/
namespace ComplexCSP.GeneratingSet

open scoped BigOperators

universe u

/-- Finite integral exponent coordinates together with lifted generators. -/
structure Coordinates (Γ : Type u) [CommGroup Γ] where
  rank : ℕ
  exponent : Additive Γ →ₗ[ℤ] (Fin rank → ℤ)
  lift : (Fin rank → ℤ) →ₗ[ℤ] Additive Γ
  exponent_lift : ∀ k, exponent (lift k) = k
  kernel_torsion : ∀ x : Γ, exponent (Additive.ofMul x) = 0 ↔ IsOfFinOrder x

/-- Actual construction of exponent coordinates for a finitely generated group. -/
theorem coordinates_nonempty (Γ : Type u) [CommGroup Γ] [Group.FG Γ] :
    Nonempty (Coordinates Γ) := by
  classical
  let M := Additive Γ
  letI : Module.Finite ℤ M := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let T : Submodule ℤ M := Submodule.torsion ℤ M
  let Q := M ⧸ T
  obtain ⟨n, b⟩ := (Module.basisOfFiniteTypeTorsionFree' (R := ℤ) (M := Q))
  obtain ⟨s, hs⟩ := Module.projective_lifting_property T.mkQ
    (LinearMap.id : Q →ₗ[ℤ] Q) T.mkQ_surjective
  let e : M →ₗ[ℤ] (Fin n → ℤ) := b.equivFun.toLinearMap.comp T.mkQ
  let l : (Fin n → ℤ) →ₗ[ℤ] M := s.comp b.equivFun.symm.toLinearMap
  refine ⟨⟨n, e, l, ?_, ?_⟩⟩
  · intro k
    have hk := LinearMap.congr_fun hs (b.equivFun.symm k)
    simp only [LinearMap.comp_apply] at hk
    change b.equivFun (T.mkQ (s (b.equivFun.symm k))) = k
    rw [hk]
    exact b.equivFun.apply_symm_apply k
  · intro x
    change b.equivFun (T.mkQ (Additive.ofMul x)) = 0 ↔ IsOfFinOrder x
    rw [LinearEquiv.map_eq_zero_iff]
    change (Submodule.Quotient.mk (Additive.ofMul x) : Q) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    change Additive.ofMul x ∈ (Submodule.torsion ℤ M).toAddSubgroup ↔ _
    rw [Submodule.torsion_int]
    exact isOfFinAddOrder_ofMul_iff

noncomputable def chooseCoordinates (Γ : Type u) [CommGroup Γ] [Group.FG Γ] :
    Coordinates Γ := Classical.choice (coordinates_nonempty Γ)

namespace Coordinates

variable {Γ : Type u} [CommGroup Γ]

/-- The additive torsion component, obtained by removing the lifted exponents. -/
def phaseAdd (c : Coordinates Γ) : Additive Γ →ₗ[ℤ] Additive Γ :=
  LinearMap.id - c.lift.comp c.exponent

@[simp] theorem exponent_phaseAdd (c : Coordinates Γ) (x : Additive Γ) :
    c.exponent (c.phaseAdd x) = 0 := by
  simp only [phaseAdd, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    map_sub, c.exponent_lift, sub_self]

theorem phaseAdd_finite_order (c : Coordinates Γ) (x : Γ) :
    IsOfFinOrder (Additive.toMul (c.phaseAdd (Additive.ofMul x))) := by
  apply (c.kernel_torsion _).mp
  exact c.exponent_phaseAdd (Additive.ofMul x)

theorem phaseAdd_of_finite_order (c : Coordinates Γ) {x : Γ} (hx : IsOfFinOrder x) :
    c.phaseAdd (Additive.ofMul x) = Additive.ofMul x := by
  simp only [phaseAdd, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    (c.kernel_torsion x).mpr hx, map_zero, sub_zero]

/-- The original element is its torsion component times the lifted free part. -/
theorem phaseAdd_decomposition (c : Coordinates Γ) (x : Additive Γ) :
    c.phaseAdd x + c.lift (c.exponent x) = x := by
  simp only [phaseAdd, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
    sub_add_cancel]

/-- The lifted free part contains no nontrivial finite-order element. -/
theorem lift_finite_order_iff (c : Coordinates Γ) (k : Fin c.rank → ℤ) :
    IsOfFinOrder (Additive.toMul (c.lift k)) ↔ k = 0 := by
  rw [← c.kernel_torsion]
  exact Iff.of_eq (congrArg (· = 0) (c.exponent_lift k))

/-- The actual lifted generators, as elements of the original group. -/
noncomputable def generator (c : Coordinates Γ) (i : Fin c.rank) : Γ :=
  Additive.toMul (c.lift (Pi.single i 1))

theorem lift_eq_sum_generators (c : Coordinates Γ) (k : Fin c.rank → ℤ) :
    c.lift k = ∑ i, k i • c.lift (Pi.single i 1) := by
  classical
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  ext j
  simp [Finset.sum_apply, Pi.single_apply]

/-- The lifted free part is exactly the displayed product of generators raised
to their integer exponents. -/
theorem lift_eq_prod_generators (c : Coordinates Γ) (k : Fin c.rank → ℤ) :
    Additive.toMul (c.lift k) = ∏ i, c.generator i ^ k i := by
  rw [c.lift_eq_sum_generators, toMul_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact toMul_zsmul (k i) (c.lift (Pi.single i 1))

/-- No nonzero integer exponent vector yields a torsion product. -/
theorem generator_independence (c : Coordinates Γ) (k : Fin c.rank → ℤ) :
    IsOfFinOrder (∏ i, c.generator i ^ k i) ↔ k = 0 := by
  rw [← c.lift_eq_prod_generators]
  exact c.lift_finite_order_iff k

/-- Every original value has the required torsion-times-generator-product form. -/
theorem generator_decomposition (c : Coordinates Γ) (x : Γ) :
    x = Additive.toMul (c.phaseAdd (Additive.ofMul x)) *
      ∏ i, c.generator i ^ c.exponent (Additive.ofMul x) i := by
  have h := congrArg Additive.toMul (c.phaseAdd_decomposition (Additive.ofMul x))
  simp only [toMul_add, c.lift_eq_prod_generators] at h
  exact h.symm

/-- The exponent vector in a torsion-times-generator decomposition is unique. -/
theorem unique_exponents (c : Coordinates Γ) (x θ : Γ)
    (hθ : IsOfFinOrder θ) (k : Fin c.rank → ℤ)
    (hx : x = θ * ∏ i, c.generator i ^ k i) :
    c.exponent (Additive.ofMul x) = k := by
  rw [← c.lift_eq_prod_generators] at hx
  rw [hx]
  change c.exponent (Additive.ofMul θ + c.lift k) = k
  rw [map_add, (c.kernel_torsion θ).mpr hθ, c.exponent_lift, zero_add]

end Coordinates
end ComplexCSP.GeneratingSet
