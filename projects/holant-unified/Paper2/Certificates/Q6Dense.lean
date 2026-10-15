import Paper2.Bell
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases

/-!
Proof-producing algebra for the four dense six-port orbit families 20--23.
These are exact scalar consequences of the displayed necessary quaternary
conditions. They do not assume a Z3 UNSAT answer. The finite orbit cover and
identification of all gadget cards remain separate proof obligations.
-/
namespace Paper2.Certificates.Q6

variable {K : Type*} [CommRing K] [NoZeroDivisors K] [CharZero K]

/-- Precisely the pair-closure/product conditions tested by the official
`complex_necessary_safe` predicate, in W4 truth-table order. -/
structure NecessarySafe (v : Fin 6 → K) : Prop where
  zero05 : v 0 = 0 ↔ v 5 = 0
  zero14 : v 1 = 0 ↔ v 4 = 0
  zero23 : v 2 = 0 ↔ v 3 = 0
  zeroProduct : v 0 * v 5 = 0 ∨ v 1 * v 4 = 0 ∨ v 2 * v 3 = 0
  products01 : v 0 * v 5 = 0 ∨ v 1 * v 4 = 0 ∨
    (v 0 * v 5)^2 = (v 1 * v 4)^2
  products02 : v 0 * v 5 = 0 ∨ v 2 * v 3 = 0 ∨
    (v 0 * v 5)^2 = (v 2 * v 3)^2
  products12 : v 1 * v 4 = 0 ∨ v 2 * v 3 = 0 ∨
    (v 1 * v 4)^2 = (v 2 * v 3)^2

omit [CharZero K] in
/-- The multiplicative equalities Q6.7 imply the disjunctions used in the
certificate predicate, over an integral domain. This is the explicit bridge
from the manuscript's polynomial equations. -/
theorem NecessarySafe.of_equations (v : Fin 6 → K)
    (h05 : v 0 = 0 ↔ v 5 = 0) (h14 : v 1 = 0 ↔ v 4 = 0)
    (h23 : v 2 = 0 ↔ v 3 = 0)
    (h0 : (v 0*v 5)*(v 1*v 4)*(v 2*v 3) = 0)
    (h01 : (v 0*v 5)*(v 1*v 4)*((v 0*v 5)^2-(v 1*v 4)^2) = 0)
    (h02 : (v 0*v 5)*(v 2*v 3)*((v 0*v 5)^2-(v 2*v 3)^2) = 0)
    (h12 : (v 1*v 4)*(v 2*v 3)*((v 1*v 4)^2-(v 2*v 3)^2) = 0) :
    NecessarySafe v := by
  refine ⟨h05, h14, h23, ?_, ?_, ?_, ?_⟩
  · simpa only [mul_eq_zero, or_assoc] using h0
  · simpa only [mul_eq_zero, sub_eq_zero, or_assoc] using h01
  · simpa only [mul_eq_zero, sub_eq_zero, or_assoc] using h02
  · simpa only [mul_eq_zero, sub_eq_zero, or_assoc] using h12

omit [CharZero K] in
theorem not_safe_full_support (v : Fin 6 → K) (hv : ∀ i, v i ≠ 0) :
    ¬ NecessarySafe v := by
  intro hs
  rcases hs.zeroProduct with h | h | h
  · exact mul_ne_zero (hv 0) (hv 5) h
  · exact mul_ne_zero (hv 1) (hv 4) h
  · exact mul_ne_zero (hv 2) (hv 3) h

omit [CharZero K] in
/-- If the first two complementary pairs are active, the third pair vanishes. -/
theorem third_pair_zero (v : Fin 6 → K) (hs : NecessarySafe v)
    (h0 : v 0 * v 5 ≠ 0) (h1 : v 1 * v 4 ≠ 0) : v 2 = 0 ∧ v 3 = 0 := by
  have h23 := hs.zeroProduct.resolve_left h0 |>.resolve_left h1
  rcases mul_eq_zero.mp h23 with h | h
  · exact ⟨h, hs.zero23.mp h⟩
  · exact ⟨hs.zero23.mpr h, h⟩

omit [CharZero K] in
theorem balanced_card_forces_middle_zero (t z : K) (ht : t ≠ 0)
    (hs : NecessarySafe ![t, z, -z, -z, z, t]) : z = 0 := by
  by_contra hz
  apply not_safe_full_support _ _ hs
  intro i
  fin_cases i <;> simp [ht, hz]

omit [CharZero K] in
/-- Unequal middle-square factors rule out the nonzero principal parameter. -/
theorem unequal_middle_card (E n m a : K) (hn : n ≠ 0) (hm : m ≠ 0)
    (hnm : n^4 - m^4 ≠ 0)
    (hs : NecessarySafe ![E, n*a^2, m*a^2, m*a^2, n*a^2, E]) : a = 0 := by
  by_contra ha
  have hna : n * a^2 ≠ 0 := mul_ne_zero hn (pow_ne_zero 2 ha)
  have hma : m * a^2 ≠ 0 := mul_ne_zero hm (pow_ne_zero 2 ha)
  have he := hs.products12.resolve_left (mul_ne_zero hna hna)
    |>.resolve_left (mul_ne_zero hma hma)
  dsimp at he
  have hzero : (n^4 - m^4) * a^8 = 0 := by
    linear_combination he
  exact mul_ne_zero hnm (pow_ne_zero 8 ha) hzero

/-- Orbit 20's identity-03 card; the endpoint expression is arbitrary. -/
theorem orbit20_principal_zero (E a : K)
    (hs : NecessarySafe ![E, 2*a^2, -6*a^2, -6*a^2, 2*a^2, E]) : a = 0 := by
  apply unequal_middle_card E 2 (-6) a (by norm_num) (by norm_num) (by norm_num)
  exact hs

/-- Both orbit-21 parameters vanish from its two displayed cards. -/
theorem orbit21_zero (t a b : K) (ht : t ≠ 0)
    (ha : NecessarySafe ![t, 2*a^2, -(2*a^2), -(2*a^2), 2*a^2, t])
    (hb : NecessarySafe ![t, 2*b^2, -(2*b^2), -(2*b^2), 2*b^2, t]) :
    a = 0 ∧ b = 0 := by
  have hza := balanced_card_forces_middle_zero t (2*a^2) ht ha
  have hzb := balanced_card_forces_middle_zero t (2*b^2) ht hb
  constructor
  · exact (sq_eq_zero_iff).mp ((mul_eq_zero.mp hza).resolve_left (by norm_num))
  · exact (sq_eq_zero_iff).mp ((mul_eq_zero.mp hzb).resolve_left (by norm_num))

/-- The two secondary orbit-22 cards force b=c=0 over any characteristic-zero
integral domain; no ordered-real or positivity reasoning is involved. -/
theorem orbit22_secondary_zero (t b c : K) (ht : t ≠ 0)
    (hprod : NecessarySafe ![t, 2*b*c, -(2*b*c), -(2*b*c), 2*b*c, t])
    (hsum : NecessarySafe ![t, b^2+c^2, -(b^2+c^2), -(b^2+c^2), b^2+c^2, t]) :
    b = 0 ∧ c = 0 := by
  have hp := balanced_card_forces_middle_zero t (2*b*c) ht hprod
  have hsum0 := balanced_card_forces_middle_zero t (b^2+c^2) ht hsum
  have hbc : b*c = 0 := by
    have : (2 : K) * (b*c) = 0 := by simpa only [mul_assoc] using hp
    exact (mul_eq_zero.mp this).resolve_left (by norm_num)
  rcases mul_eq_zero.mp hbc with hb | hc
  · refine ⟨hb, ?_⟩
    simpa [hb] using hsum0
  · refine ⟨?_, hc⟩
    simpa [hc] using hsum0

/-- Orbit 22 after its two secondary parameters have vanished. -/
theorem orbit22_principal_zero (E a : K)
    (hs : NecessarySafe ![E, 2*a^2, -4*a^2, -4*a^2, 2*a^2, E]) : a = 0 := by
  apply unequal_middle_card E 2 (-4) a (by norm_num) (by norm_num) (by norm_num)
  exact hs

/-- The first orbit-23 card forces its b parameter to vanish. -/
theorem orbit23_first (t a b c d : K) (ht : t ≠ 0)
    (hs : NecessarySafe ![t, 2*b^2, -a*c-a*d-2*b^2,
      a*c+a*d-2*b^2, 2*b^2, t]) : b = 0 := by
  by_contra hb
  have hmiddle : 2*b^2 ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hb)
  obtain ⟨h2, h3⟩ := third_pair_zero _ hs (mul_ne_zero ht ht)
    (mul_ne_zero hmiddle hmiddle)
  dsimp at h2 h3
  have hz : (4 : K) * b^2 = 0 := by
    linear_combination -h2 - h3
  exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hb) hz

omit [CharZero K] in
/-- After b=0, a nonzero principal parameter in the second orbit-23 card
forces both residual parameters to vanish. -/
theorem orbit23_second (t a c d : K) (ht : t ≠ 0) (ha : a ≠ 0)
    (hs : NecessarySafe ![t, c*d, a*d, -a*c, c*d, t]) : c = 0 ∧ d = 0 := by
  have hclosure : a*d = 0 ↔ -a*c = 0 := hs.zero23
  by_cases hc : c = 0
  · refine ⟨hc, ?_⟩
    have hd : a*d = 0 := hclosure.mpr (by simp [hc])
    exact (mul_eq_zero.mp hd).resolve_left ha
  · have hd : d ≠ 0 := by
      intro hd
      have : -a*c = 0 := hclosure.mp (by simp [hd])
      exact mul_ne_zero (neg_ne_zero.mpr ha) hc this
    exact False.elim (not_safe_full_support _ (by
      intro i
      fin_cases i <;> simp [ht, ha, hc, hd]) hs)

/-- The final orbit-23 card excludes its principal parameter. -/
theorem orbit23_principal_zero (t a : K) (ht : t ≠ 0)
    (hs : NecessarySafe ![t, 3*a^2, -(3*a^2), -(3*a^2), 3*a^2, t]) : a = 0 := by
  have hz := balanced_card_forces_middle_zero t (3*a^2) ht hs
  exact (sq_eq_zero_iff).mp ((mul_eq_zero.mp hz).resolve_left (by norm_num))


/-- All three dense orbit-22 parameters vanish from the exact three cards. -/
theorem orbit22_zero (t a b c : K) (ht : t ≠ 0)
    (hprod : NecessarySafe ![t, 2*b*c, -(2*b*c), -(2*b*c), 2*b*c, t])
    (hsum : NecessarySafe ![t, b^2+c^2, -(b^2+c^2), -(b^2+c^2), b^2+c^2, t])
    (hprincipal : NecessarySafe ![-2*a^2-2*b*c+t, 2*a^2+2*a*b-2*a*c,
      -4*a^2-2*b*c, -4*a^2-2*b*c, 2*a^2-2*a*b+2*a*c, -2*a^2-2*b*c+t]) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨hb, hc⟩ := orbit22_secondary_zero t b c ht hprod hsum
  refine ⟨?_, hb, hc⟩
  apply orbit22_principal_zero (-2*a^2+t) a
  simpa [hb, hc] using hprincipal

/-- The exact three-card dense orbit-23 implication. Only its final two
complementary coordinates can survive, represented here by the free c,d. -/
theorem orbit23_reduction (t a b c d : K) (ht : t ≠ 0)
    (hfirst : NecessarySafe ![t, 2*b^2, -a*c-a*d-2*b^2,
      a*c+a*d-2*b^2, 2*b^2, t])
    (hsecond : NecessarySafe ![t, -b^2+c*d, a*b+a*d+b^2-b*d,
      a*b-a*c+b^2+b*c, -b^2+c*d, t])
    (hthird : NecessarySafe ![t, 3*a^2-a*b-a*d+b*d,
      -3*a^2+a*b-a*c-b*d, -3*a^2+a*b+a*d+b*c,
      3*a^2-a*b+a*c-b*c, t]) : a = 0 ∧ b = 0 := by
  have hb := orbit23_first t a b c d ht hfirst
  refine ⟨?_, hb⟩
  by_contra ha
  have hs : NecessarySafe ![t, c*d, a*d, -a*c, c*d, t] := by
    simpa [hb, neg_mul] using hsecond
  obtain ⟨hc, hd⟩ := orbit23_second t a c d ht ha hs
  apply ha
  apply orbit23_principal_zero t a ht
  simpa [hb, hc, hd, neg_mul] using hthird

end Paper2.Certificates.Q6
