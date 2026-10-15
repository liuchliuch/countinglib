import Paper2.DegreeCSP.AffineLiveCoordinates
import Paper2.DegreeCSP.BooleanAffineParityMinorLinear

/-! Exact independent-coordinate parametrization and pinned parity projections.
Every existential witness is an original supported Boolean word. -/
namespace Paper2.DegreeCSP.BooleanAffineParityMinor
open Tractable
open BooleanStructure (indicator)
open Holant.ReedMuller.FlatNetwork (vectorWord wordVector boolEquiv vector_word word_vector)
open BooleanAffineParityMinorLinear
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {n r : ℕ}

def coordinateProjection (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (q : Fin r → Fin n) : D →ₗ[ZMod 2] (Fin r → ZMod 2) where
  toFun v j := v.val (q j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordinateEquiv (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (q : Fin r → Fin n)
    (h : Function.Bijective (fun v : D => fun j => v.val (q j))) :
    D ≃ₗ[ZMod 2] (Fin r → ZMod 2) :=
  LinearEquiv.ofBijective (coordinateProjection D q) h

def coordinateForm {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (e : D ≃ₗ[ZMod 2] (Fin r → ZMod 2)) (t : Fin n) :
    (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj t).comp (D.subtype.comp e.symm.toLinearMap)

def parameterWord {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (a : Fin n → Bool) (e : D ≃ₗ[ZMod 2] (Fin r → ZMod 2))
    (v : Fin r → ZMod 2) : Fin n → Bool :=
  wordVector (vectorWord a + (e.symm v).val)

theorem parameterWord_coordinate {D : Submodule (ZMod 2) (Fin n → ZMod 2)}
    (a : Fin n → Bool) (e : D ≃ₗ[ZMod 2] (Fin r → ZMod 2)) (v) (t) :
    parameterWord a e v t = boolEquiv.symm (boolEquiv (a t) + coordinateForm e t v) := rfl

theorem coordinateForm_selected (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (q : Fin r → Fin n) (h) (v : Fin r → ZMod 2) (j : Fin r) :
    coordinateForm (coordinateEquiv D q h) (q j) v = v j := by
  exact congrFun ((coordinateEquiv D q h).apply_symm_apply v) j

theorem parameterWord_selected (D : Submodule (ZMod 2) (Fin n → ZMod 2))
    (a : Fin n → Bool) (q : Fin r → Fin n) (h) (v : Fin r → ZMod 2) (j : Fin r) :
    parameterWord a (coordinateEquiv D q h) v (q j) =
      boolEquiv.symm (boolEquiv (a (q j)) + v j) := by
  rw [parameterWord_coordinate, coordinateForm_selected]

/-- Pin all independent coordinates except the two selected input bits. -/
def Pinned (a : Fin n → Bool) (q : Fin r → Fin n) (i j : Fin r)
    (x : Fin n → Bool) : Prop :=
  ∀ ℓ, ℓ ≠ i → ℓ ≠ j → x (q ℓ) = a (q ℓ)

/-- A literal projection of one pinned source relation. -/
def PinnedProjection (R : Set (Fin n → Bool)) (a : Fin n → Bool)
    (q : Fin r → Fin n) (i j : Fin r) (t : Fin n) (z : Fin 3 → Bool) : Prop :=
  ∃ x ∈ R, x (q i) = z 0 ∧ x (q j) = z 1 ∧ x t = z 2 ∧ Pinned a q i j x

theorem translated_bit_eq (a b : Bool) (v : ZMod 2) :
    boolEquiv.symm (boolEquiv a + v) = b ↔ v = boolEquiv a + boolEquiv b := by
  constructor
  · intro h
    have he := congrArg boolEquiv h
    rw [Equiv.apply_symm_apply] at he
    have hc := CharTwo.add_self_eq_zero (boolEquiv a)
    linear_combination he - hc
  · intro h
    rw [h, ←add_assoc, CharTwo.add_self_eq_zero, zero_add, Equiv.symm_apply_apply]

theorem boolEquiv_xor (a b : Bool) :
    boolEquiv (Bool.xor a b) = boolEquiv a + boolEquiv b := by
  cases a <;> cases b <;> decide

theorem field_parity (a b c u v w : Bool) :
    boolEquiv w = boolEquiv c + (boolEquiv a + boolEquiv u) +
        (boolEquiv b + boolEquiv v) ↔
      w = Bool.xor (Bool.xor u v) (Bool.xor (Bool.xor a b) c) := by
  have he : boolEquiv (Bool.xor (Bool.xor u v) (Bool.xor (Bool.xor a b) c)) =
      boolEquiv c + (boolEquiv a + boolEquiv u) + (boolEquiv b + boolEquiv v) := by
    simp only [boolEquiv_xor]
    ac_rfl
  rw [←he]
  exact boolEquiv.apply_eq_iff_eq

/-- Two active linear coefficients give exactly the affine ternary parity
relation after genuine coordinate pins and existential projection. -/
theorem pinned_projection_parity (R : Set (Fin n → Bool)) (a : Fin n → Bool)
    (q : Fin r → Fin n) (p : (Fin r → ZMod 2) → (Fin n → Bool))
    (L : Fin n → ((Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2))
    (hp : ∀ v t, p v t = boolEquiv.symm (boolEquiv (a t) + L t v))
    (hselected : ∀ v ℓ, L (q ℓ) v = v ℓ)
    (hmem : ∀ v, p v ∈ R) (hsurj : ∀ x ∈ R, ∃ v, p v = x)
    {i j : Fin r} (hij : i ≠ j) (t : Fin n)
    (hi : L t (Pi.single i 1) = 1) (hj : L t (Pi.single j 1) = 1) :
    ∀ z, PinnedProjection R a q i j t z ↔
      z 2 = Bool.xor (Bool.xor (z 0) (z 1))
        (Bool.xor (Bool.xor (a (q i)) (a (q j))) (a t)) := by
  classical
  intro z
  let b := boolEquiv (a (q i)) + boolEquiv (z 0)
  let d := boolEquiv (a (q j)) + boolEquiv (z 1)
  have hsel (v : Fin r → ZMod 2) (ℓ : Fin r) :
      p v (q ℓ) = boolEquiv.symm (boolEquiv (a (q ℓ)) + v ℓ) := by
    rw [hp, hselected]
  constructor
  · rintro ⟨x, hx, hxi, hxj, hxt, hpin⟩
    obtain ⟨v, rfl⟩ := hsurj x hx
    have hvi : v i = b := (translated_bit_eq _ _ _).mp (by simpa only [hsel] using hxi)
    have hvj : v j = d := (translated_bit_eq _ _ _).mp (by simpa only [hsel] using hxj)
    have hv : v = twoVector i j b d := by
      funext ℓ
      by_cases hli : ℓ = i
      · subst ℓ
        rw [twoVector_apply_left hij, hvi]
      · by_cases hlj : ℓ = j
        · subst ℓ
          rw [twoVector_apply_right hij, hvj]
        · rw [twoVector_apply_other hli hlj]
          have he := (translated_bit_eq _ _ _).mp
            (by simpa only [hsel] using hpin ℓ hli hlj)
          simpa only [CharTwo.add_self_eq_zero] using he
    have hout : boolEquiv (z 2) = boolEquiv (a t) + b + d := by
      rw [hp, hv, twoVector_parity (L t) hi hj] at hxt
      have he := congrArg boolEquiv hxt
      rw [Equiv.apply_symm_apply] at he
      exact he.symm.trans (add_assoc _ _ _).symm
    exact (field_parity _ _ _ _ _ _).mp hout
  · intro hz
    let v := twoVector i j b d
    have hout : boolEquiv (z 2) = boolEquiv (a t) + b + d :=
      (field_parity _ _ _ _ _ _).mpr hz
    refine ⟨p v, hmem v, ?_, ?_, ?_, ?_⟩
    · rw [hsel, show v = twoVector i j b d from rfl, twoVector_apply_left hij]
      exact (translated_bit_eq _ _ _).mpr rfl
    · rw [hsel, show v = twoVector i j b d from rfl, twoVector_apply_right hij]
      exact (translated_bit_eq _ _ _).mpr rfl
    · rw [hp, twoVector_parity (L t) hi hj]
      apply boolEquiv.injective
      rw [Equiv.apply_symm_apply]
      exact (add_assoc _ _ _).symm.trans hout.symm
    · intro ℓ hli hlj
      rw [hsel, show v = twoVector i j b d from rfl,
        twoVector_apply_other hli hlj, add_zero, Equiv.symm_apply_apply]

/-- Pinning the independent coordinates makes every projected support fiber
contain at most one source word. This permits exact coefficient sums. -/
theorem pinned_projection_unique (R : Set (Fin n → Bool)) (a : Fin n → Bool)
    (q : Fin r → Fin n)
    (hproj : Function.Injective (GeneratedCoordinateMarginal.liveProjection (indicator R) q))
    (i j : Fin r) (z : Fin 3 → Bool) (x y : Fin n → Bool)
    (hx : x ∈ R) (hy : y ∈ R)
    (hxi : x (q i) = z 0) (hyi : y (q i) = z 0)
    (hxj : x (q j) = z 1) (hyj : y (q j) = z 1)
    (hxp : Pinned a q i j x) (hyp : Pinned a q i j y) : x = y := by
  have he : (⟨x, (BooleanStructure.indicator_ne_zero R x).mpr hx⟩ :
      GeneratedCoordinateMarginal.Live (indicator R)) =
      ⟨y, (BooleanStructure.indicator_ne_zero R y).mpr hy⟩ := by
    apply hproj
    funext ℓ
    by_cases hli : ℓ = i
    · subst ℓ
      exact hxi.trans hyi.symm
    · by_cases hlj : ℓ = j
      · subst ℓ
        exact hxj.trans hyj.symm
      · exact (hxp ℓ hli hlj).trans (hyp ℓ hli hlj).symm
  exact congrArg Subtype.val he

end
end Paper2.DegreeCSP.BooleanAffineParityMinor
