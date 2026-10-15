import Mathlib.Tactic

/-! The final coefficient step of the odd-dihedral six-port proof. Actual
three-phase determinant equations force all six face minors of the eight
nonzero block coefficients to vanish, hence a product of three binaries. -/
namespace Paper2.HeightOne.Dihedral
noncomputable section
variable {K : Type*} [Field K]

theorem quadratic_three_roots (a b c s t u : K)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hs : a + b * s + c * s ^ 2 = 0)
    (ht : a + b * t + c * t ^ 2 = 0)
    (hu : a + b * u + c * u ^ 2 = 0) : a = 0 ∧ b = 0 ∧ c = 0 := by
  have hst' : b + c * (s + t) = 0 := by
    apply (mul_eq_zero.mp (show (s - t) * (b + c * (s + t)) = 0 by
      linear_combination hs - ht)).resolve_left (sub_ne_zero.mpr hst)
  have hsu' : b + c * (s + u) = 0 := by
    apply (mul_eq_zero.mp (show (s - u) * (b + c * (s + u)) = 0 by
      linear_combination hs - hu)).resolve_left (sub_ne_zero.mpr hsu)
  have hc : c = 0 :=
    (mul_eq_zero.mp (show c * (t - u) = 0 by
      linear_combination hst' - hsu')).resolve_right (sub_ne_zero.mpr htu)
  have hb : b = 0 := by simpa [hc] using hst'
  exact ⟨by simpa [hb, hc] using hs, hb, hc⟩

def detTwo (A : Bool → Bool → K) : K :=
  A false false * A true true - A false true * A true false

/-- No root-of-unity assumption is needed for this coefficient extraction. -/
theorem pencil_det_endpoint_faces (A B : Bool → Bool → K) (s t u : K)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hs : detTwo (fun i j => A i j - s * B i j) = 0)
    (ht : detTwo (fun i j => A i j - t * B i j) = 0)
    (hu : detTwo (fun i j => A i j - u * B i j) = 0) :
    detTwo A = 0 ∧ detTwo B = 0 := by
  let b := -(A false false * B true true + B false false * A true true) +
    A false true * B true false + B false true * A true false
  have hp (r : K) : detTwo (fun i j => A i j - r * B i j) =
      detTwo A + b * r + detTwo B * r ^ 2 := by dsimp [detTwo, b]; ring
  obtain ⟨hA, _, hB⟩ := quadratic_three_roots (detTwo A) b (detTwo B) s t u
    hst hsu htu (by rwa [← hp]) (by rwa [← hp]) (by rwa [← hp])
  exact ⟨hA, hB⟩

def cubeFacesZero (c : Bool → Bool → Bool → K) : Prop :=
  (∀ w, detTwo (fun u v => c u v w) = 0) ∧
  (∀ v, detTwo (fun u w => c u v w) = 0) ∧
  (∀ u, detTwo (fun v w => c u v w) = 0)

def cubePhaseDeterminants (c : Bool → Bool → Bool → K) (s : K) : Prop :=
  detTwo (fun u v => c u v false - s * c u v true) = 0 ∧
  detTwo (fun u w => c u false w - s * c u true w) = 0 ∧
  detTwo (fun v w => c false v w - s * c true v w) = 0

theorem cube_faces_of_three_phases (c : Bool → Bool → Bool → K) (s t u : K)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hs : cubePhaseDeterminants c s) (ht : cubePhaseDeterminants c t)
    (hu : cubePhaseDeterminants c u) : cubeFacesZero c := by
  have h₁ := pencil_det_endpoint_faces (fun u v => c u v false)
    (fun u v => c u v true) s t u hst hsu htu hs.1 ht.1 hu.1
  have h₂ := pencil_det_endpoint_faces (fun u w => c u false w)
    (fun u w => c u true w) s t u hst hsu htu hs.2.1 ht.2.1 hu.2.1
  have h₃ := pencil_det_endpoint_faces (fun v w => c false v w)
    (fun v w => c true v w) s t u hst hsu htu hs.2.2 ht.2.2 hu.2.2
  exact ⟨fun w => by cases w; exact h₁.1; exact h₁.2,
    fun v => by cases v; exact h₂.1; exact h₂.2,
    fun u => by cases u; exact h₃.1; exact h₃.2⟩

theorem cube_factorization_of_faces (c : Bool → Bool → Bool → K)
    (hn : ∀ u v w, c u v w ≠ 0) (hf : cubeFacesZero c) :
    ∀ u v w, c u v w = c false false false *
      (if u then c true false false / c false false false else 1) *
      (if v then c false true false / c false false false else 1) *
      (if w then c false false true / c false false false else 1) := by
  have h₀ := hn false false false
  have h₁ := hn true false false
  have hxy := hf.1 false
  have hxz := hf.2.1 false
  have hyz := hf.2.2 false
  have hyz' := hf.2.2 true
  dsimp [detTwo] at hxy hxz hyz hyz'
  have h110 : c true true false = c true false false * c false true false /
      c false false false := by
    apply (eq_div_iff h₀).mpr
    linear_combination hxy
  have h101 : c true false true = c true false false * c false false true /
      c false false false := by
    apply (eq_div_iff h₀).mpr
    linear_combination hxz
  have h011 : c false true true = c false true false * c false false true /
      c false false false := by
    apply (eq_div_iff h₀).mpr
    linear_combination hyz
  have h111 : c true true true = c true false false * c false true false *
      c false false true / c false false false ^ 2 := by
    apply (mul_left_cancel₀ h₁)
    have he : c true false false * c true true true =
        c true false true * c true true false := sub_eq_zero.mp hyz'
    rw [he, h101, h110]
    ring
  intro u v w
  cases u <;> cases v <;> cases w <;>
    simp only [Bool.false_eq_true, ↓reduceIte, mul_one, h110, h101, h011, h111]
    <;> field_simp <;> ring

theorem cube_factorization_of_three_phases (c : Bool → Bool → Bool → K)
    (hn : ∀ u v w, c u v w ≠ 0) (s t u : K)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hs : cubePhaseDeterminants c s) (ht : cubePhaseDeterminants c t)
    (hu : cubePhaseDeterminants c u) :
    ∃ a r₁ r₂ r₃ : K, a ≠ 0 ∧ r₁ ≠ 0 ∧ r₂ ≠ 0 ∧ r₃ ≠ 0 ∧
      ∀ i j k, c i j k = a * (if i then r₁ else 1) *
        (if j then r₂ else 1) * (if k then r₃ else 1) := by
  exact ⟨c false false false, c true false false / c false false false,
    c false true false / c false false false, c false false true / c false false false,
    hn _ _ _, div_ne_zero (hn _ _ _) (hn _ _ _),
    div_ne_zero (hn _ _ _) (hn _ _ _), div_ne_zero (hn _ _ _) (hn _ _ _),
    cube_factorization_of_faces c hn (cube_faces_of_three_phases c s t u hst hsu htu hs ht hu)⟩

end
end Paper2.HeightOne.Dihedral

