import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi

/-! Finite binary linear forms and the two active coordinates of a parity minor. -/
namespace Paper2.DegreeCSP.BooleanAffineParityMinorLinear
noncomputable section

variable {r : ℕ}

/-- The literal coefficient of an original coordinate. -/
def coefficient (L : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) (j : Fin r) : ZMod 2 :=
  L (Pi.single j 1)

/-- Expand a finite linear form in the actual coordinate singleton vectors. -/
theorem expansion (L : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (x : Fin r → ZMod 2) :
    L x = ∑ j, x j * L (Pi.single j 1) := by
  conv_lhs => rw [pi_eq_sum_univ' x]
  simp only [map_sum, map_smul, smul_eq_mul]

theorem binary_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A binary linear form is zero, a coordinate, or has two distinct active
original coordinates. This includes the empty function space. -/
theorem dichotomy (L : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2) :
    L = 0 ∨ (∃ j, ∀ x, L x = x j) ∨
      ∃ i j, i ≠ j ∧ L (Pi.single i 1) = 1 ∧ L (Pi.single j 1) = 1 := by
  classical
  by_cases hz : ∀ j, L (Pi.single j 1) = 0
  · left
    apply LinearMap.ext
    intro x
    change L x = 0
    rw [expansion]
    simp [hz]
  · right
    obtain ⟨i, hi⟩ := not_forall.mp hz
    have hi1 : L (Pi.single i 1) = 1 := (binary_cases _).resolve_left hi
    by_cases ho : ∀ j, j ≠ i → L (Pi.single j 1) = 0
    · left
      refine ⟨i, ?_⟩
      intro x
      rw [expansion, Finset.sum_eq_single i]
      · simp [hi1]
      · intro j hj hji
        simp [ho j hji]
      · simp
    · right
      obtain ⟨j, hj⟩ := not_forall.mp ho
      have hji : j ≠ i := by
        by_contra he
        exact hj (fun hn => (hn he).elim)
      have hj0 : L (Pi.single j 1) ≠ 0 := by
        intro h0
        exact hj (fun _ => h0)
      exact ⟨i, j, hji.symm, hi1, (binary_cases _).resolve_left hj0⟩

/-- Place two field bits on their literal original singleton coordinates. -/
def twoVector (i j : Fin r) (b d : ZMod 2) : Fin r → ZMod 2 :=
  b • Pi.single i 1 + d • Pi.single j 1

theorem twoVector_apply_left {i j : Fin r} (hij : i ≠ j) (b d : ZMod 2) :
    twoVector i j b d i = b := by
  simp [twoVector, hij]

theorem twoVector_apply_right {i j : Fin r} (hij : i ≠ j) (b d : ZMod 2) :
    twoVector i j b d j = d := by
  simp [twoVector, hij.symm]

theorem twoVector_apply_other {i j ℓ : Fin r} (hli : ℓ ≠ i) (hlj : ℓ ≠ j)
    (b d : ZMod 2) : twoVector i j b d ℓ = 0 := by
  simp [twoVector, hli, hlj]

/-- Two active coefficients give the literal two-bit parity form. -/
theorem twoVector_parity (L : (Fin r → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    {i j : Fin r} (hi : L (Pi.single i 1) = 1) (hj : L (Pi.single j 1) = 1)
    (b d : ZMod 2) : L (twoVector i j b d) = b + d := by
  simp only [twoVector, map_add, map_smul, smul_eq_mul, hi, hj, mul_one]

end
end Paper2.DegreeCSP.BooleanAffineParityMinorLinear
