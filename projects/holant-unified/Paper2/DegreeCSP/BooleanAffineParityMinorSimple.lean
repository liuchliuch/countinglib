import Paper2.DegreeCSP.BooleanAffineParityMinorLinear
import Paper2.DegreeCSP.BooleanSupport
import Holant.ReedMuller.FlatNetwork.Coordinates

/-! Simple affine coordinates preserve discriminator; a non-product support
therefore has an actual coordinate with two active linear coefficients. -/
namespace Paper2.DegreeCSP.BooleanAffineParityMinorSimple
open Tractable BooleanStructure
open Holant.ReedMuller.FlatNetwork (boolEquiv)
noncomputable section

variable {r n : ℕ}

/-- The field version of the literal Boolean discriminator. -/
def fieldDiscriminator (u v w : ZMod 2) : ZMod 2 := if u = v then w else u

theorem fieldDiscriminator_bool (u v w : ZMod 2) :
    fieldDiscriminator u v w =
      boolEquiv (discriminator (boolEquiv.symm u, boolEquiv.symm v, boolEquiv.symm w)) := by
  have he : boolEquiv.symm u = boolEquiv.symm v ↔ u = v :=
    boolEquiv.symm.injective.eq_iff
  simp only [fieldDiscriminator, discriminator, he]
  split_ifs <;> simp

/-- Translation by an actual Boolean anchor commutes with discriminator. -/
theorem translated_discriminator (a : Bool) (u v w : ZMod 2) :
    boolEquiv.symm (boolEquiv a + fieldDiscriminator u v w) =
      discriminator (boolEquiv.symm (boolEquiv a + u),
        boolEquiv.symm (boolEquiv a + v), boolEquiv.symm (boolEquiv a + w)) := by
  have he : boolEquiv.symm (boolEquiv a + u) = boolEquiv.symm (boolEquiv a + v) ↔
      u = v := by
    constructor
    · intro h
      exact add_left_cancel (boolEquiv.symm.injective h)
    · intro h
      rw [h]
  simp only [fieldDiscriminator, discriminator, he]
  split_ifs <;> rfl

/-- Apply the discriminator to the independent field coordinates. -/
def fieldCombination (u v w : Fin r → ZMod 2) : Fin r → ZMod 2 :=
  fun j => fieldDiscriminator (u j) (v j) (w j)

theorem parametrization_discriminator
    (p : (Fin r → ZMod 2) → (Fin n → Bool)) (a : Fin n → Bool)
    (L : Fin n → ((Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (hp : ∀ v t, p v t = boolEquiv.symm (boolEquiv (a t) + L t v))
    (hsimple : ∀ t, L t = 0 ∨ ∃ j, ∀ v, L t v = v j)
    (u v w : Fin r → ZMod 2) :
    p (fieldCombination u v w) = fun t => discriminator (p u t, p v t, p w t) := by
  funext t
  rw [hp, hp, hp, hp]
  rcases hsimple t with hzero | ⟨j, hj⟩
  · rw [hzero]
    simp only [LinearMap.zero_apply, add_zero, discriminator, ite_true]
  · rw [hj, hj, hj, hj]
    exact translated_discriminator (a t) (u j) (v j) (w j)

/-- An onto affine parametrization with only constant and single-coordinate
linear parts gives literal discriminator closure of the relation. -/
theorem preserves_discriminator (R : Set (Fin n → Bool))
    (p : (Fin r → ZMod 2) → (Fin n → Bool)) (a : Fin n → Bool)
    (L : Fin n → ((Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (hp : ∀ v t, p v t = boolEquiv.symm (boolEquiv (a t) + L t v))
    (himage : ∀ v, p v ∈ R) (hsurj : ∀ x ∈ R, ∃ v, p v = x)
    (hsimple : ∀ t, L t = 0 ∨ ∃ j, ∀ v, L t v = v j) :
    Preserves discriminator R := by
  intro x hx y hy z hz
  obtain ⟨u, rfl⟩ := hsurj x hx
  obtain ⟨v, rfl⟩ := hsurj y hy
  obtain ⟨w, rfl⟩ := hsurj z hz
  rw [← parametrization_discriminator p a L hp hsimple u v w]
  exact himage (fieldCombination u v w)

/-- If the support indicator is outside the actual product class, at least
one original affine coordinate has two distinct active singleton inputs. -/
theorem exists_nonsimple_coordinate (R : Set (Fin n → Bool))
    (hnon : ¬ Product (indicator R))
    (p : (Fin r → ZMod 2) → (Fin n → Bool)) (a : Fin n → Bool)
    (L : Fin n → ((Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (hp : ∀ v t, p v t = boolEquiv.symm (boolEquiv (a t) + L t v))
    (himage : ∀ v, p v ∈ R) (hsurj : ∀ x ∈ R, ∃ v, p v = x) :
    ∃ t i j, i ≠ j ∧ L t (Pi.single i 1) = 1 ∧ L t (Pi.single j 1) = 1 := by
  classical
  by_contra hn
  have hs : ∀ t, L t = 0 ∨ ∃ j, ∀ v, L t v = v j := by
    intro t
    rcases BooleanAffineParityMinorLinear.dichotomy (L t) with hzero | hsingle | htwo
    · exact Or.inl hzero
    · exact Or.inr hsingle
    · obtain ⟨i, j, hij, hi, hj⟩ := htwo
      exact False.elim (hn ⟨t, i, j, hij, hi, hj⟩)
  exact hnon (product_indicator_of_discriminator R
    (preserves_discriminator R p a L hp himage hsurj hs))

end
end Paper2.DegreeCSP.BooleanAffineParityMinorSimple
