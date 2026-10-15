import ComplexCSP.Algebra.AlgebraicInput
import ComplexCSP.Algebra.ComplexRootCertificatesIsolation
import Mathlib.RingTheory.Localization.Integral

/-!
# Coverage of the separate polynomial-and-rectangle input representation

Every algebraic complex number has a literal integer coefficient list and a
rational isolating rectangle. Original input polynomials need not be monic,
irreducible, or square-free. Clearing denominators and isolating distinct roots
are mathematical existence proofs establishing representation coverage.
-/

namespace ComplexCSP.AlgebraicEncoding

open Polynomial ComplexRootCertificates

/-- All semantic integer polynomials have an ascending finite coefficient list. -/
theorem exists_integerListPolynomial (p : Polynomial ℤ) :
    ∃ a : List ℤ, integerListPolynomial a = p := by
  let a := List.ofFn (fun i : Fin (p.natDegree+1) ↦ p.coeff i.val)
  refine ⟨a, ?_⟩
  apply Polynomial.ext
  intro k
  rw [integerListPolynomial_coeff]
  by_cases hk : k < p.natDegree+1
  · rw [List.getD_eq_getElem a 0 (by simpa [a] using hk)]
    simp only [a, List.getElem_ofFn]
  · rw [List.getD_eq_default a 0 (by simpa [a] using le_of_not_gt hk),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- Rational denominator clearing produces a nonzero integer annihilator; no
integrality of the algebraic value itself is assumed. -/
theorem exists_integer_annihilator (z : ℂ) (hz : IsAlgebraic ℚ z) :
    ∃ p : Polynomial ℤ, p ≠ 0 ∧ Polynomial.aeval z p = 0 :=
  (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hz

/-- Coverage of the literal separate algebraic-number representation. -/
theorem exists_algebraicInput_represents (z : ℂ) (hz : IsAlgebraic ℚ z) :
    ∃ a : AlgebraicInput, a.Represents z := by
  obtain ⟨p,hp,hroot⟩ := exists_integer_annihilator z hz
  obtain ⟨a,ha⟩ := exists_integerListPolynomial p
  have hpcomplex : p.map (Int.castRingHom ℂ) ≠ 0 := by
    intro h
    exact hp ((Polynomial.map_eq_zero_iff Int.cast_injective).mp h)
  have hrootcomplex : (p.map (Int.castRingHom ℂ)).eval z = 0 := by
    rw [Polynomial.eval_map]
    exact hroot
  obtain ⟨box,hbox,hunique⟩ := exists_isolating_rectangle
    (p.map (Int.castRingHom ℂ)) hpcomplex z hrootcomplex
  refine ⟨⟨a,box⟩, ?_⟩
  change integerListPolynomial a ≠ 0 ∧ evalIntegerList a z = 0 ∧ box.Contains z ∧ _
  refine ⟨ha ▸ hp, ?_, hbox, ?_⟩
  · rw [← integerListPolynomial_aeval, ha]
    exact hroot
  · intro w hwroot hwbox
    apply hunique w hwbox.closed
    rw [Polynomial.eval_map]
    rw [← integerListPolynomial_aeval, ha] at hwroot
    exact hwroot

/-- The represented complex values are exactly the algebraic ones. -/
theorem algebraicInput_represents_iff_isAlgebraic (z : ℂ) :
    (∃ a : AlgebraicInput, a.Represents z) ↔ IsAlgebraic ℚ z :=
  ⟨fun ⟨_,h⟩ ↦ h.isAlgebraic, exists_algebraicInput_represents z⟩

end ComplexCSP.AlgebraicEncoding
