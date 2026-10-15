import ComplexCSP.Algebra.GeneratingSetPrimes

/-!
# Construction of a prime-based purification map

Starting with a finitely generated subgroup realization, the exponent map,
torsion phase and first-prime amplitude are constructed. The structural
PurificationMap interface is then filled by proofs. No injective purification
map or norm-one characterization is assumed here.
-/
namespace ComplexCSP.GeneratingSet

open Purification
open scoped BigOperators

universe u

namespace Coordinates
variable {Γ : Type u} [CommGroup Γ]

def exponentHom (c : Coordinates Γ) : Γ →* Multiplicative (Fin c.rank → ℤ) where
  toFun x := Multiplicative.ofAdd (c.exponent (Additive.ofMul x))
  map_one' := by change c.exponent 0 = 0; exact map_zero _
  map_mul' x y := by
    change c.exponent (Additive.ofMul x + Additive.ofMul y) =
      c.exponent (Additive.ofMul x) + c.exponent (Additive.ofMul y)
    exact map_add _ _ _

def phaseHom (c : Coordinates Γ) (original : Γ →* ℂˣ) : Γ →* ℂˣ where
  toFun x := original (Additive.toMul (c.phaseAdd (Additive.ofMul x)))
  map_one' := by change original (Additive.toMul (c.phaseAdd 0)) = 1; simp
  map_mul' x y := by
    change original (Additive.toMul (c.phaseAdd (Additive.ofMul x + Additive.ofMul y))) = _
    rw [map_add, toMul_add, map_mul]

theorem phaseHom_norm (c : Coordinates Γ) (original : Γ →* ℂˣ) (x : Γ) :
    ‖(c.phaseHom original x : ℂ)‖ = 1 :=
  (((Units.coeHom ℂ).comp original).isOfFinOrder (c.phaseAdd_finite_order x)).norm_eq_one

theorem phaseHom_torsion (c : Coordinates Γ) (original : Γ →* ℂˣ)
    {x : Γ} (hx : IsOfFinOrder x) : c.phaseHom original x = original x := by
  change original (Additive.toMul (c.phaseAdd (Additive.ofMul x))) = original x
  rw [c.phaseAdd_of_finite_order hx]
  rfl

end Coordinates

/-- First-prime amplitudes, embedded exactly from positive rationals into ℂ. -/
noncomputable def complexPrimeProduct (n : ℕ) :
    Multiplicative (Fin n → ℤ) →* ℂˣ :=
  (Units.map (algebraMap ℚ ℂ).toMonoidHom).comp (primeProduct n)

theorem complexPrimeProduct_norm (n : ℕ) (k : Multiplicative (Fin n → ℤ)) :
    ‖(complexPrimeProduct n k : ℂ)‖ = ((primeProduct n k : ℚ) : ℝ) := by
  change ‖((primeProduct n k : ℚ) : ℂ)‖ = ((primeProduct n k : ℚ) : ℝ)
  rw [← Complex.ofReal_ratCast]
  have hp : (0 : ℝ) < ((primeProduct n k : ℚ) : ℝ) := by exact_mod_cast primeProduct_pos n k
  simpa only [Complex.norm_real, Real.norm_eq_abs] using abs_of_pos hp

theorem complexPrimeProduct_norm_one_iff (n : ℕ) (k : Multiplicative (Fin n → ℤ)) :
    ‖(complexPrimeProduct n k : ℂ)‖ = 1 ↔ k = 1 := by
  rw [complexPrimeProduct_norm]
  constructor
  · intro h
    have hq : (primeProduct n k : ℚ) = 1 := by exact_mod_cast h
    apply primeProduct_injective n
    apply Units.ext
    simpa only [map_one, Units.val_one] using hq
  · intro h
    subst k
    simp

namespace Coordinates
variable {Γ : Type u} [CommGroup Γ]

/-- The actual prime-based homomorphism, before denominator clearing. -/
noncomputable def purifiedHom (c : Coordinates Γ) (original : Γ →* ℂˣ) : Γ →* ℂˣ :=
  c.phaseHom original * (complexPrimeProduct c.rank).comp c.exponentHom

theorem purifiedHom_norm_one_iff (c : Coordinates Γ) (original : Γ →* ℂˣ) (x : Γ) :
    ‖(c.purifiedHom original x : ℂ)‖ = 1 ↔ IsOfFinOrder x := by
  change ‖((c.phaseHom original x : ℂ) *
    (complexPrimeProduct c.rank (c.exponentHom x) : ℂ))‖ = 1 ↔ _
  rw [norm_mul, c.phaseHom_norm, one_mul, complexPrimeProduct_norm_one_iff]
  change c.exponent (Additive.ofMul x) = 0 ↔ IsOfFinOrder x
  exact c.kernel_torsion x

theorem purifiedHom_torsion (c : Coordinates Γ) (original : Γ →* ℂˣ)
    {x : Γ} (hx : IsOfFinOrder x) : c.purifiedHom original x = original x := by
  change c.phaseHom original x * complexPrimeProduct c.rank (c.exponentHom x) = original x
  have he : c.exponentHom x = 1 := (c.kernel_torsion x).mpr hx
  rw [he, map_one, mul_one, c.phaseHom_torsion original hx]

theorem purifiedHom_injective (c : Coordinates Γ) (original : Γ →* ℂˣ)
    (hinj : Function.Injective original) : Function.Injective (c.purifiedHom original) := by
  intro x y hxy
  have hdiv : c.purifiedHom original (x / y) = 1 := by simp only [map_div, hxy, div_self']
  have ht : IsOfFinOrder (x / y) := (c.purifiedHom_norm_one_iff original _).mp (by rw [hdiv]; simp)
  have horig : original (x / y) = 1 := by rw [← c.purifiedHom_torsion original ht, hdiv]
  have hsource : x / y = 1 := hinj (by simpa only [map_one] using horig)
  exact div_eq_one.mp hsource

/-- All fields of the structural interface are now proved from constructed
coordinates and prime amplitudes. -/
noncomputable def purificationMap (c : Coordinates Γ) (original : Γ →* ℂˣ)
    (hinj : Function.Injective original) : PurificationMap Γ original where
  hom := c.purifiedHom original
  injective := c.purifiedHom_injective original hinj
  fixes_torsion := fun _ hx => c.purifiedHom_torsion original hx
  norm_one_iff := c.purifiedHom_norm_one_iff original

end Coordinates

/-- Existence of a genuine prime-based purification for every finitely generated
abelian group with its injective original complex realization. -/
theorem purificationMap_nonempty (Γ : Type u) [CommGroup Γ] [Group.FG Γ]
    (original : Γ →* ℂˣ) (hinj : Function.Injective original) :
    Nonempty (PurificationMap Γ original) :=
  ⟨(chooseCoordinates Γ).purificationMap original hinj⟩

end ComplexCSP.GeneratingSet
