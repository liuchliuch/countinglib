import Paper2.CommonPhase.PairSum
import Paper2.CommonPhase.MatchingDeck

/-! Common phase follows from genuine double contractions of a literal matching
deck. No scalar-ratio premise and no realizability premise is used. -/
namespace Paper2.CommonPhase
open EndpointSelfLoop
variable {ι : Type} {K : Type*}

/-- The manuscript's normalized contraction deck, including actual residual ports. -/
def MatchingDeck [Semiring K] (F : Tensor K ι) (lam : PortPair ι → K)
    (P : (e : PortPair ι) → XMatching (Remaining e.first e.second)) : Prop :=
  ∀ e, loop e.first e.second e.distinct F = fun x => lam e * literal (P e) K x

namespace PortPair

theorem pairSum_mul [Semiring K] (e : PortPair ι) (c : K) (F : Tensor K ι) :
    e.pairSum (fun x => c * F x) = fun x => c * e.pairSum F x := by
  funext x
  simp only [pairSum, Finset.mul_sum]

theorem pairSum_deck [Semiring K] {F : Tensor K ι} {lam : PortPair ι → K}
    {P : (e : PortPair ι) → XMatching (Remaining e.first e.second)}
    (h : MatchingDeck F lam P) (e : PortPair ι) :
    e.pairSum F = fun x => lam e * literal (P e) K (restrict e.first e.second x) := by
  funext x
  rw [pairSum_eq_loop, h]

/-- The coefficient of a residual literal after one further actual X loop. -/
noncomputable def doubleLiteral [Semiring K] (e f : PortPair ι) (h : e.Disjoint f)
    (P : XMatching (Remaining e.first e.second)) (x : ι → Bool) : K :=
  (e.residual f h).pairSum (literal P K) (restrict e.first e.second x)

theorem doubleLiteral_range [Semiring K] (e f : PortPair ι) (h : e.Disjoint f)
    (P : XMatching (Remaining e.first e.second)) (x : ι → Bool) :
    e.doubleLiteral f h P x = (0 : K) ∨ e.doubleLiteral f h P x = (1 : K) ∨
      e.doubleLiteral f h P x = (2 : K) := by
  unfold doubleLiteral
  rw [pairSum_eq_loop]
  exact loop_literal_eq_zero_or_one_or_two P _ _ _ _

theorem doubleLiteral_exists [Semiring K] (e f : PortPair ι) (h : e.Disjoint f)
    (P : XMatching (Remaining e.first e.second)) :
    ∃ x : ι → Bool, e.doubleLiteral f h P x = (1 : K) ∨
      e.doubleLiteral f h P x = (2 : K) := by
  let q := e.residual f h
  obtain ⟨y, hy⟩ := exists_loop_literal_eq_one_or_two (K := K) P q.first q.second q.distinct
  refine ⟨extendPair e.first e.second e.distinct
    (extendPair q.first q.second q.distinct y false) false, ?_⟩
  simp only [doubleLiteral, restrict_extend, pairSum_eq_loop]
  change loop q.first q.second q.distinct (literal P K)
    (restrict q.first q.second (extendPair q.first q.second q.distinct y false)) = 1 ∨
    loop q.first q.second q.distinct (literal P K)
    (restrict q.first q.second (extendPair q.first q.second q.distinct y false)) = 2
  simpa only [restrict_extend] using hy

/-- Equality of two orders, with their original scalar coefficients retained. -/
theorem double_deck_eq [Semiring K] {F : Tensor K ι} {lam : PortPair ι → K}
    {P : (e : PortPair ι) → XMatching (Remaining e.first e.second)}
    (hd : MatchingDeck F lam P) (e f : PortPair ι) (h : e.Disjoint f) (x : ι → Bool) :
    lam e * e.doubleLiteral f h (P e) x =
      lam f * f.doubleLiteral e h.symm (P f) x := by
  have hc := congrFun (pairSum_comm h F) x
  rw [pairSum_deck hd e, pairSum_deck hd f, pairSum_mul, pairSum_mul] at hc
  simpa only [pairSum_lift e f h, pairSum_lift f e h.symm, doubleLiteral] using hc.symm

end PortPair

/-- Multiplication by a strictly positive real number, preserving complex phase. -/
def PositiveRatio (a b : ℂ) : Prop := ∃ r : ℝ, 0 < r ∧ a = (r : ℂ) * b

theorem PositiveRatio.trans {a b c : ℂ} (hab : PositiveRatio a b)
    (hbc : PositiveRatio b c) : PositiveRatio a c := by
  obtain ⟨r, hr, he⟩ := hab
  obtain ⟨s, hs, hf⟩ := hbc
  refine ⟨r*s, mul_pos hr hs, ?_⟩
  rw [he, hf, Complex.ofReal_mul, mul_assoc]

theorem PositiveRatio.symm {a b : ℂ} (hab : PositiveRatio a b) : PositiveRatio b a := by
  obtain ⟨r, hr, he⟩ := hab
  refine ⟨r⁻¹, inv_pos.mpr hr, ?_⟩
  rw [he, Complex.ofReal_inv, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact Complex.ofReal_ne_zero.mpr (ne_of_gt hr)

/-- A nonzero equality of positive 1-or-2 multiples fixes a positive phase ratio. -/
theorem positiveRatio_of_one_two {a b u v : ℂ} (ha : a ≠ 0)
    (hu : u = 1 ∨ u = 2) (hv : v = 0 ∨ v = 1 ∨ v = 2)
    (he : a * u = b * v) : PositiveRatio a b := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · simp at he
    exact False.elim (ha he)
  · refine ⟨1, by norm_num, ?_⟩
    simpa using he
  · refine ⟨2, by norm_num, ?_⟩
    simpa [mul_comm] using he
  · have : a = 0 := by simpa using he
    exact False.elim (ha this)
  · refine ⟨1/2, by norm_num, ?_⟩
    push_cast
    linear_combination he / 2
  · refine ⟨1, by norm_num, ?_⟩
    push_cast
    linear_combination he / 2

/-- The sharper manuscript ratio, retaining the actual multiplicities 1 and 2. -/
theorem ratio_of_one_two {a b u v : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hu : u = 1 ∨ u = 2) (hv : v = 0 ∨ v = 1 ∨ v = 2)
    (he : a * u = b * v) : a / b = 1 ∨ a / b = 2 ∨ a / b = (2 : ℂ)⁻¹ := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact False.elim (ha (by simpa using he))
  · left
    apply (div_eq_iff hb).mpr
    simpa using he
  · right; left
    apply (div_eq_iff hb).mpr
    simpa [mul_comm] using he
  · exact False.elim (ha (by simpa using he))
  · right; right
    apply (div_eq_iff hb).mpr
    linear_combination he / 2
  · left
    apply (div_eq_iff hb).mpr
    linear_combination he / 2

/-- Exact adjacent-pair ratios, proved by evaluating commuting double contractions. -/
theorem matching_deck_disjoint_ratio {F : Tensor ℂ ι} {lam : PortPair ι → ℂ}
    {P : (e : PortPair ι) → XMatching (Remaining e.first e.second)}
    (hd : MatchingDeck F lam P) (hnz : ∀ e, lam e ≠ 0)
    (e f : PortPair ι) (h : e.Disjoint f) :
    lam e / lam f = 1 ∨ lam e / lam f = 2 ∨ lam e / lam f = (2 : ℂ)⁻¹ := by
  obtain ⟨x, hx⟩ := e.doubleLiteral_exists (K := ℂ) f h (P e)
  exact ratio_of_one_two (hnz e) (hnz f) hx
    (f.doubleLiteral_range e h.symm (P f) x) (PortPair.double_deck_eq hd e f h x)

/-- Local phase agreement is derived from actual finite-sum contractions. -/
theorem matching_deck_disjoint_positive {F : Tensor ℂ ι} {lam : PortPair ι → ℂ}
    {P : (e : PortPair ι) → XMatching (Remaining e.first e.second)}
    (hd : MatchingDeck F lam P) (hnz : ∀ e, lam e ≠ 0)
    (e f : PortPair ι) (h : e.Disjoint f) : PositiveRatio (lam e) (lam f) := by
  obtain ⟨x, hx⟩ := e.doubleLiteral_exists (K := ℂ) f h (P e)
  exact positiveRatio_of_one_two (hnz e) hx
    (f.doubleLiteral_range e h.symm (P f) x) (PortPair.double_deck_eq hd e f h x)

/-- The disjoint-pair graph is connected, and all deck scalars have one phase. -/
theorem matching_deck_positive [Fintype ι] (hn : 6 ≤ Fintype.card ι)
    {F : Tensor ℂ ι} {lam : PortPair ι → ℂ}
    {P : (e : PortPair ι) → XMatching (Remaining e.first e.second)}
    (hd : MatchingDeck F lam P) (hnz : ∀ e, lam e ≠ 0) (e f : PortPair ι) :
    PositiveRatio (lam e) (lam f) := by
  obtain ⟨g, heg, hfg⟩ := PortPair.exists_common_disjoint hn e f
  exact (matching_deck_disjoint_positive hd hnz e g heg).trans
    (matching_deck_disjoint_positive hd hnz f g hfg).symm

end Paper2.CommonPhase
