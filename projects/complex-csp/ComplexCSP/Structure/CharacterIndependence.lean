import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Monoid characters and finite coefficient grouping

This file formalizes the algebraic core of Lemma 5.6 and the coefficient-grouping
step of the universal identity oracle in the Cai--Chen decidability manuscript.
Character equality is an explicit input to the executable test below. No procedure
for deciding equality of arbitrary monoid homomorphisms is postulated here.
-/

namespace ComplexCSP

open scoped BigOperators

section Independence

variable {M K ι : Type*} [Monoid M] [Field K]

/-- Distinct unital multiplicative characters are linearly independent.
This is Dedekind independence from mathlib, restricted along an injective family.
The characteristic-zero assumption of the paper is not needed. -/
theorem characters_linearIndependent (χ : ι → M →* K)
    (hχ : Function.Injective χ) :
    LinearIndependent K (fun i => (χ i : M → K)) :=
  (linearIndependent_monoidHom M K).comp χ hχ

/-- Paper Lemma 5.6, with a finite index set and an explicit pointwise relation. -/
theorem character_coefficients_eq_zero (χ : ι → M →* K)
    (hχ : Function.Injective χ) (s : Finset ι) (c : ι → K)
    (h : ∀ x : M, ∑ i ∈ s, c i * χ i x = 0) :
    ∀ i ∈ s, c i = 0 := by
  apply (linearIndependent_iff'.mp (characters_linearIndependent χ hχ)) s c
  ext x
  simpa using h x

/-- The finite relation vanishes identically exactly when every coefficient does. -/
theorem character_relation_zero_iff (χ : ι → M →* K)
    (hχ : Function.Injective χ) (s : Finset ι) (c : ι → K) :
    (∀ x : M, ∑ i ∈ s, c i * χ i x = 0) ↔ ∀ i ∈ s, c i = 0 := by
  constructor
  · exact character_coefficients_eq_zero χ hχ s c
  · intro h x
    exact Finset.sum_eq_zero fun i hi => by rw [h i hi, zero_mul]

end Independence

section Grouping

variable {M K ι : Type*} [Monoid M] [Field K]
variable [DecidableEq (M →* K)]

/-- Sum the coefficients belonging to one character-equality class.
The supplied character equality procedure is used by the finite filter. -/
def characterClassCoefficient (s : Finset ι) (χ : ι → M →* K)
    (c : ι → K) (ψ : M →* K) : K :=
  ∑ i ∈ s with χ i = ψ, c i

/-- Deduplicate the finitely many characters occurring in a finite expression. -/
def characterClasses (s : Finset ι) (χ : ι → M →* K) : Finset (M →* K) :=
  s.image χ

/-- Regrouping a character expression by equal characters preserves its value. -/
theorem sum_grouped_characters (s : Finset ι) (χ : ι → M →* K)
    (c : ι → K) (x : M) :
    (∑ ψ ∈ characterClasses s χ, characterClassCoefficient s χ c ψ * ψ x) =
      ∑ i ∈ s, c i * χ i x := by
  calc
    _ = ∑ ψ ∈ s.image χ, ∑ i ∈ s with χ i = ψ, c i * χ i x := by
      apply Finset.sum_congr rfl
      intro ψ hψ
      rw [characterClassCoefficient, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun i hi => Finset.mem_image_of_mem χ hi) _

/-- The algebraic finite zero criterion used in the universal identity oracle.
Repeated characters are allowed, and their coefficient sums must vanish. -/
theorem grouped_character_zero_iff (s : Finset ι) (χ : ι → M →* K)
    (c : ι → K) :
    (∀ x : M, ∑ i ∈ s, c i * χ i x = 0) ↔
      ∀ ψ ∈ characterClasses s χ, characterClassCoefficient s χ c ψ = 0 := by
  have hid : Function.Injective (id : (M →* K) → M →* K) := Function.injective_id
  rw [← character_relation_zero_iff id hid (characterClasses s χ)
    (characterClassCoefficient s χ c)]
  simp only [id_eq, sum_grouped_characters]

/-- A nonzero class sum guarantees an actual monoid element witnessing failure. -/
theorem exists_character_counterexample (s : Finset ι) (χ : ι → M →* K)
    (c : ι → K) (h : ∃ ψ ∈ characterClasses s χ,
      characterClassCoefficient s χ c ψ ≠ 0) :
    ∃ x : M, ∑ i ∈ s, c i * χ i x ≠ 0 := by
  classical
  by_contra! hn
  obtain ⟨ψ, hψ, hc⟩ := h
  exact hc ((grouped_character_zero_iff s χ c).mp hn ψ hψ)

variable [DecidableEq K]

/-- A terminating finite test, relative to the explicitly supplied field equality
and character equality procedures. This definition does not invoke `Classical`. -/
def characterZeroTest (s : Finset ι) (χ : ι → M →* K) (c : ι → K) : Bool :=
  decide (∀ ψ ∈ characterClasses s χ, characterClassCoefficient s χ c ψ = 0)

/-- Soundness and completeness of the finite test for pointwise universal zero. -/
theorem characterZeroTest_correct (s : Finset ι) (χ : ι → M →* K) (c : ι → K) :
    characterZeroTest s χ c = true ↔ (∀ x : M, ∑ i ∈ s, c i * χ i x = 0) := by
  rw [grouped_character_zero_iff]
  simp [characterZeroTest]

/-- Rejection is equivalent to existence of a genuine counterexample. -/
theorem characterZeroTest_rejects_iff (s : Finset ι) (χ : ι → M →* K) (c : ι → K) :
    characterZeroTest s χ c = false ↔ (∃ x : M, ∑ i ∈ s, c i * χ i x ≠ 0) := by
  classical
  rw [← Bool.not_eq_true, characterZeroTest_correct]
  push_neg
  rfl

end Grouping

section FiniteComparisonTable

variable {M K ι : Type*} [Monoid M] [Field K] [DecidableEq K]

/-- A finite equality matrix suffices: sum the coefficients whose indices are
reported equal to a given index. No equality decision on the infinite type of
all monoid characters is needed by this computation. -/
def indexedCharacterClassCoefficient (s : Finset ι) (same : ι → ι → Bool)
    (c : ι → K) (j : ι) : K :=
  ∑ i ∈ s with same i j = true, c i

/-- Executable quadratic-size finite zero test from a supplied equality matrix.
Testing a repeated class more than once is harmless and avoids representative
selection entirely. -/
def indexedCharacterZeroTest (s : Finset ι) (same : ι → ι → Bool)
    (c : ι → K) : Bool :=
  decide (∀ j ∈ s, indexedCharacterClassCoefficient s same c j = 0)

/-- A verified comparison procedure is needed only for pairs occurring in the
finite input. It converts the executable test into a universal identity test. -/
theorem indexedCharacterZeroTest_correct (s : Finset ι) (χ : ι → M →* K)
    (same : ι → ι → Bool) (c : ι → K)
    (hsame : ∀ i ∈ s, ∀ j ∈ s, same i j = true ↔ χ i = χ j) :
    indexedCharacterZeroTest s same c = true ↔
      (∀ x : M, ∑ i ∈ s, c i * χ i x = 0) := by
  classical
  have hcoef (j : ι) (hj : j ∈ s) :
      indexedCharacterClassCoefficient s same c j =
        characterClassCoefficient s χ c (χ j) := by
    unfold indexedCharacterClassCoefficient characterClassCoefficient
    congr 1
    ext i
    simp only [Finset.mem_filter]
    exact and_congr_right (fun hi => hsame i hi j hj)
  rw [grouped_character_zero_iff]
  simp only [indexedCharacterZeroTest, decide_eq_true_eq, characterClasses,
    Finset.mem_image, forall_exists_index, and_imp]
  constructor
  · intro h ψ j hj hχ
    subst ψ
    exact (hcoef j hj).symm.trans (h j hj)
  · intro h j hj
    exact (hcoef j hj).trans (h (χ j) j hj rfl)

/-- The matrix-based test rejects precisely when some monoid element violates
the identity. Counterexample existence is classical; the Bool test itself is not. -/
theorem indexedCharacterZeroTest_rejects_iff (s : Finset ι) (χ : ι → M →* K)
    (same : ι → ι → Bool) (c : ι → K)
    (hsame : ∀ i ∈ s, ∀ j ∈ s, same i j = true ↔ χ i = χ j) :
    indexedCharacterZeroTest s same c = false ↔
      (∃ x : M, ∑ i ∈ s, c i * χ i x ≠ 0) := by
  classical
  rw [← Bool.not_eq_true, indexedCharacterZeroTest_correct s χ same c hsame]
  push_neg
  rfl

end FiniteComparisonTable

end ComplexCSP
