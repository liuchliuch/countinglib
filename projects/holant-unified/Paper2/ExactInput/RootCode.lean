import Paper2.Tractable.Scalars
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.DeriveEncodable
import Mathlib.Tactic.Linarith

/-!
Adapted isolated-root mathematical foundation, independently checked in Paper 2.
Finite exact rational polynomial / complex rectangle descriptions for 2.13.
Representation and coverage below are mathematical theorems, not a runtime
root isolation algorithm. `Represents` deliberately has no Decidable instance.
All descriptors can be enumerated effectively; rejecting the invalid ones and
computing arithmetic between independently isolated roots remain open.
-/

namespace Paper2.ExactInput
open Polynomial

/-- Sparse rational polynomials, with repetitions and zero terms allowed. -/
abbrev RationalPolynomialCode := List (ℕ × ℚ)

namespace RationalPolynomialCode

noncomputable def polynomial : RationalPolynomialCode → ℚ[X]
  | [] => 0
  | (k, q) :: rest => Polynomial.monomial k q + polynomial rest

@[simp] theorem polynomial_append (a b : RationalPolynomialCode) :
    polynomial (a ++ b) = polynomial a + polynomial b := by
  induction a with
  | nil => simp [polynomial]
  | cons t ts ih => cases t; simp [polynomial, ih, add_assoc]

/-- Finite coefficient data covers every polynomial, without selecting it at runtime. -/
theorem exists_code (p : ℚ[X]) : ∃ c : RationalPolynomialCode, polynomial c = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨a, rfl⟩ := hp
    obtain ⟨b, rfl⟩ := hq
    exact ⟨a ++ b, polynomial_append a b⟩
  | monomial k q => exact ⟨[(k, q)], by simp [polynomial]⟩

/-- Genuine executable exact rational evaluation of the raw polynomial. -/
def evalRational (x : ℚ) : RationalPolynomialCode → ℚ
  | [] => 0
  | (k, q) :: rest => q * x ^ k + evalRational x rest

theorem evalRational_correct (x : ℚ) (c : RationalPolynomialCode) :
    evalRational x c = (polynomial c).eval x := by
  induction c with
  | nil => simp [evalRational, polynomial]
  | cons t ts ih => cases t; simp [evalRational, polynomial, ih]

end RationalPolynomialCode

structure RationalRectangle where
  reLower : ℚ
  reUpper : ℚ
  imLower : ℚ
  imUpper : ℚ
  deriving DecidableEq, Encodable

namespace RationalRectangle

def Contains (r : RationalRectangle) (z : ℂ) : Prop :=
  (r.reLower : ℝ) < z.re ∧ z.re < (r.reUpper : ℝ) ∧
    (r.imLower : ℝ) < z.im ∧ z.im < (r.imUpper : ℝ)

/-- The descriptor's elementary shape check is computable. This is not a root count. -/
def ordered (r : RationalRectangle) : Bool :=
  decide (r.reLower < r.reUpper ∧ r.imLower < r.imUpper)

/-- Conjugation is an executable change of rational rectangle endpoints. -/
def conjugate (r : RationalRectangle) : RationalRectangle :=
  ⟨r.reLower, r.reUpper, -r.imUpper, -r.imLower⟩

@[simp] theorem contains_conjugate (r : RationalRectangle) (z : ℂ) :
    r.conjugate.Contains z ↔ r.Contains (star z) := by
  simp only [Contains, conjugate, Complex.star_def, Complex.conj_re,
    Complex.conj_im, Rat.cast_neg]
  constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;>
    refine ⟨h₁, h₂, ?_, ?_⟩ <;> linarith

theorem ordered_of_contains {r : RationalRectangle} {z : ℂ} (h : r.Contains z) :
    r.ordered = true := by
  simp only [ordered, decide_eq_true_eq]
  constructor
  · exact_mod_cast h.1.trans h.2.1
  · exact_mod_cast h.2.2.1.trans h.2.2.2

/-- Rational endpoints isolate any specified real coordinate from a finite set.
This is a coverage proof; its induction over semantic real numbers is not an algorithm. -/
theorem exists_isolating_interval (s : Finset ℝ) (a : ℝ) :
    ∃ l u : ℚ, (l : ℝ) < a ∧ a < (u : ℝ) ∧
      ∀ b ∈ s, (l : ℝ) < b → b < (u : ℝ) → b = a := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    obtain ⟨l, _, hl⟩ := exists_rat_btwn (show a - 1 < a by linarith)
    obtain ⟨u, hu, _⟩ := exists_rat_btwn (show a < a + 1 by linarith)
    exact ⟨l, u, hl, hu, by simp⟩
  | @insert b s hbs ih =>
    obtain ⟨l, u, hl, hu, hs⟩ := ih
    rcases lt_trichotomy b a with hba | hba | hab
    · obtain ⟨c, hc, hca⟩ := exists_rat_btwn (max_lt hl hba)
      refine ⟨c, u, hca, hu, ?_⟩
      intro w hw hcw hwu
      rcases Finset.mem_insert.mp hw with hwb | hw
      · subst w
        have hb := lt_of_le_of_lt (le_max_right (l : ℝ) b) hc
        exact False.elim ((lt_trans hb hcw).false)
      · exact hs w hw (lt_trans (lt_of_le_of_lt (le_max_left (l : ℝ) b) hc) hcw) hwu
    · subst b
      refine ⟨l, u, hl, hu, ?_⟩
      intro w hw hwl hwu
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rfl
      · exact hs w hw hwl hwu
    · obtain ⟨c, hac, hc⟩ := exists_rat_btwn (lt_min hu hab)
      refine ⟨l, c, hl, hac, ?_⟩
      intro w hw hwl hwc
      rcases Finset.mem_insert.mp hw with hwb | hw
      · subst w
        have hb := lt_of_lt_of_le hc (min_le_right (u : ℝ) b)
        exact False.elim ((lt_trans hwc hb).false)
      · exact hs w hw hwl (lt_trans hwc (lt_of_lt_of_le hc (min_le_left (u : ℝ) b)))

theorem exists_isolating_rectangle (s : Finset ℂ) (z : ℂ) :
    ∃ r : RationalRectangle, r.Contains z ∧ ∀ w ∈ s, r.Contains w → w = z := by
  classical
  obtain ⟨rl, ru, hrl, hru, hr⟩ := exists_isolating_interval (s.image Complex.re) z.re
  obtain ⟨il, iu, hil, hiu, hi⟩ := exists_isolating_interval (s.image Complex.im) z.im
  refine ⟨⟨rl, ru, il, iu⟩, ⟨hrl, hru, hil, hiu⟩, ?_⟩
  intro w hw hwbox
  apply Complex.ext
  · exact hr w.re (Finset.mem_image.mpr ⟨w, hw, rfl⟩) hwbox.1 hwbox.2.1
  · exact hi w.im (Finset.mem_image.mpr ⟨w, hw, rfl⟩) hwbox.2.2.1 hwbox.2.2.2

end RationalRectangle

structure RootCode where
  coefficients : RationalPolynomialCode
  rectangle : RationalRectangle
  deriving DecidableEq, Encodable

namespace RootCode

noncomputable def polynomial (c : RootCode) : ℚ[X] := c.coefficients.polynomial

/-- A relational decoder: no choice function or validity oracle is installed. -/
def Represents (c : RootCode) (z : ℂ) : Prop :=
  c.polynomial ≠ 0 ∧ c.rectangle.Contains z ∧ Polynomial.aeval z c.polynomial = 0 ∧
    ∀ w : ℂ, c.rectangle.Contains w → Polynomial.aeval w c.polynomial = 0 → w = z

theorem represents_unique {c : RootCode} {z w : ℂ}
    (hz : c.Represents z) (hw : c.Represents w) : z = w :=
  (hz.2.2.2 w hw.2.1 hw.2.2.1).symm

theorem represents_isAlgebraic {c : RootCode} {z : ℂ} (h : c.Represents z) :
    IsAlgebraic ℚ z := ⟨c.polynomial, h.1, h.2.2.1⟩

def conjugate (c : RootCode) : RootCode :=
  ⟨c.coefficients, c.rectangle.conjugate⟩

theorem represents_conjugate {c : RootCode} {z : ℂ} (h : c.Represents z) :
    c.conjugate.Represents (star z) := by
  have he (w : ℂ) : Polynomial.aeval (star w) c.polynomial =
      star (Polynomial.aeval w c.polynomial) := by
    simpa using Polynomial.aeval_algHom_apply (Complex.conjAe.restrictScalars ℚ)
      w c.polynomial
  refine ⟨h.1, ?_, ?_, ?_⟩
  · simpa only [conjugate, RationalRectangle.contains_conjugate, star_star] using h.2.1
  · change Polynomial.aeval (star z) c.polynomial = 0
    rw [he, h.2.2.1, star_zero]
  · intro w hwbox hwroot
    change Polynomial.aeval w c.polynomial = 0 at hwroot
    have hwbox' : c.rectangle.Contains (star w) :=
      (RationalRectangle.contains_conjugate c.rectangle w).mp hwbox
    have hwroot' : Polynomial.aeval (star w) c.polynomial = 0 := by
      rw [he, hwroot, star_zero]
    have hw := h.2.2.2 (star w) hwbox' hwroot'
    simpa only [star_star] using congrArg star hw

/-- Every algebraic complex number has a minimal-polynomial descriptor with a
genuine isolating rational rectangle. No effective construction is claimed here. -/
theorem exists_minimal_code (z : ℂ) (hz : IsAlgebraic ℚ z) :
    ∃ c : RootCode, c.Represents z ∧ c.polynomial = minpoly ℚ z := by
  classical
  let p := minpoly ℚ z
  have hp : p ≠ 0 := minpoly.ne_zero hz.isIntegral
  let roots : Finset ℂ := (p.map (algebraMap ℚ ℂ)).roots.toFinset
  have mem_roots (w : ℂ) (hw : Polynomial.aeval w p = 0) : w ∈ roots := by
    apply Multiset.mem_toFinset.mpr
    exact (Polynomial.mem_roots_map_of_injective
      (algebraMap ℚ ℂ).injective hp).mpr hw
  obtain ⟨r, hr, hiso⟩ := RationalRectangle.exists_isolating_rectangle roots z
  obtain ⟨a, ha⟩ := RationalPolynomialCode.exists_code p
  let c : RootCode := ⟨a, r⟩
  have hc : c.polynomial = p := ha
  refine ⟨c, ?_, hc⟩
  refine ⟨by simpa only [hc] using hp, hr, ?_, ?_⟩
  · simpa only [hc] using minpoly.aeval ℚ z
  · intro w hwbox hw
    apply hiso w
    · exact mem_roots w (by simpa only [hc] using hw)
    · exact hwbox

/-- Source AlgebraicComplex uses exactly the same algebraic-closure subfield. -/
theorem exists_code (z : Paper2.Tractable.AlgebraicComplex) :
    ∃ c : RootCode, c.Represents (z : ℂ) := by
  have hz : IsAlgebraic ℚ (z : ℂ) := mem_algebraicClosure_iff.mp z.property
  obtain ⟨c, hc, _⟩ := exists_minimal_code (z : ℂ) hz
  exact ⟨c, hc⟩

/-- Literal paper input: monic irreducible polynomial and a unique isolated root.
The generic `Represents` relation alone is deliberately insufficient. -/
def MinimalRepresents (c : RootCode) (z : ℂ) : Prop :=
  c.Represents z ∧ c.polynomial.Monic ∧ Irreducible c.polynomial

theorem minimalRepresents_unique {c : RootCode} {z w : ℂ}
    (hz : c.MinimalRepresents z) (hw : c.MinimalRepresents w) : z = w :=
  represents_unique hz.1 hw.1

theorem minimalRepresents_polynomial {c : RootCode} {z : ℂ}
    (h : c.MinimalRepresents z) : c.polynomial = minpoly ℚ z := by
  exact minpoly.eq_of_irreducible_of_monic h.2.2 h.1.2.2.1 h.2.1

theorem minimal_coverage (z : Paper2.Tractable.AlgebraicComplex) :
    ∃ c : RootCode, c.MinimalRepresents (z : ℂ) := by
  have hz : IsAlgebraic ℚ (z : ℂ) := mem_algebraicClosure_iff.mp z.property
  obtain ⟨c, hc, hp⟩ := exists_minimal_code (z : ℂ) hz
  exact ⟨c, hc, hp ▸ minpoly.monic hz.isIntegral,
    hp ▸ minpoly.irreducible hz.isIntegral⟩

theorem minimalRepresents_conjugate {c : RootCode} {z : ℂ}
    (h : c.MinimalRepresents z) : c.conjugate.MinimalRepresents (star z) :=
  ⟨represents_conjugate h.1, h.2⟩

/-- Validity is semantic root isolation, not a decidable predicate supplied by choice. -/
def Valid (c : RootCode) : Prop := ∃ z : ℂ, c.MinimalRepresents z

/-- Semantic interpretation only. No executable root-isolation algorithm is claimed. -/
noncomputable def value (c : RootCode) (h : c.Valid) : Paper2.Tractable.AlgebraicComplex :=
  ⟨h.choose, mem_algebraicClosure_iff.mpr (represents_isAlgebraic h.choose_spec.1)⟩

theorem value_spec (c : RootCode) (h : c.Valid) :
    c.MinimalRepresents (c.value h : ℂ) := h.choose_spec

theorem value_eq {c : RootCode} (h : c.Valid) {z : Paper2.Tractable.AlgebraicComplex}
    (hz : c.MinimalRepresents (z : ℂ)) : c.value h = z :=
  Subtype.ext (minimalRepresents_unique (value_spec c h) hz)

end RootCode
end Paper2.ExactInput
