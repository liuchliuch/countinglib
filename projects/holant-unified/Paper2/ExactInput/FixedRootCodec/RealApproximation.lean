import Paper2.ExactInput.FixedRootCodec.BisectionMachine
import Holant.Proofs.AlgebraicRecognition.RealIsolation
import Mathlib.FieldTheory.Perfect

/-! Semantic correctness of the actual common-denominator bisection program.
Every fixed real algebraic constant has rational bracket data; those data are
selected once from separability and derivative continuity before runtime.
No successful root-search witness is assumed for a varying input answer. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity Polynomial
open Holant.LocalDrafts.EffectiveAlgebraic
noncomputable section

abbrev RealInterval := RealIsolation.Interval

def stateInterval (s : BisectionState) : RealInterval :=
  ⟨mkRat s.1 s.2.2,mkRat s.2.1 s.2.2⟩

theorem evalRational_same (p : Paper2.ExactInput.RationalPolynomialCode) (x : ℚ) :
    Holant.LocalDrafts.EffectiveAlgebraic.RationalPolynomialCode.evalRational x p =
      Paper2.ExactInput.RationalPolynomialCode.evalRational x p := by
  induction p with
  | nil => rfl
  | cons t ps ih =>
    rcases t with ⟨k,a⟩
    simp only [Holant.LocalDrafts.EffectiveAlgebraic.RationalPolynomialCode.evalRational,
      Paper2.ExactInput.RationalPolynomialCode.evalRational,ih]

theorem interval_midpoint (s : BisectionState) (hq : 0 < s.2.2) :
    (stateInterval s).midpoint = midpoint s := by
  have hn : (s.2.2 : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [stateInterval,RealIsolation.Interval.midpoint,midpoint,
    Rat.mkRat_eq_divInt,Rat.divInt_eq_div]
  push_cast
  field_simp
  <;> ring

theorem double_ratio (a : ℤ) (q : ℕ) (hq : 0 < q) :
    mkRat (a + a) (2 * q) = mkRat a q := by
  have hn : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  simp only [Rat.mkRat_eq_divInt,Rat.divInt_eq_div]
  push_cast
  field_simp
  <;> ring

theorem interval_bisect (p : Paper2.ExactInput.RationalPolynomialCode)
    (s : BisectionState) (hq : 0 < s.2.2) :
    stateInterval (bisect p s) = RealIsolation.bisect p (stateInterval s) := by
  unfold bisect RealIsolation.bisect
  dsimp only
  rw [interval_midpoint s hq,evalRational_same]
  split_ifs <;> simp only [stateInterval,double_ratio _ _ hq,midpoint]

theorem interval_iterate (p : Paper2.ExactInput.RationalPolynomialCode)
    (s : BisectionState) (hq : 0 < s.2.2) (k : ℕ) :
    stateInterval ((bisect p)^[k] s) = RealIsolation.refine p (stateInterval s) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',interval_bisect,ih]
    · rfl
    · rw [bisection_denominator]
      positivity

/-- Rational data and proved local monotonicity for a fixed real constant. -/
structure RealBracket (a : ℝ) where
  polynomial : Holant.LocalDrafts.EffectiveAlgebraic.RationalPolynomialCode
  interval : RealInterval
  contains : interval.Contains a
  root : Polynomial.aeval a polynomial.polynomial = 0
  brackets : RealIsolation.Brackets polynomial interval
  monotone : StrictMonoOn (fun x : ℝ => Polynomial.aeval x polynomial.polynomial)
    (Set.Icc (interval.lower : ℝ) interval.upper)

theorem RealBracket.refine_contains {a : ℝ} (b : RealBracket a) (k : ℕ) :
    (RealIsolation.refine b.polynomial b.interval k).Contains a := by
  obtain ⟨y,hy,hr⟩ := RealIsolation.brackets_exists
    (RealIsolation.refine_brackets b.brackets k)
  have hs := RealIsolation.refine_bounds b.brackets k
  have hl : (b.interval.lower : ℝ) ≤ (RealIsolation.refine b.polynomial b.interval k).lower :=
    by exact_mod_cast hs.1
  have hu : ((RealIsolation.refine b.polynomial b.interval k).upper : ℝ) ≤ b.interval.upper :=
    by exact_mod_cast hs.2
  have he : y = a := b.monotone.injOn ⟨hl.trans hy.1,hy.2.trans hu⟩ b.contains
    (hr.trans b.root.symm)
  simpa only [he] using hy

theorem RealBracket.width_bound {a : ℝ} (b : RealBracket a) (k : ℕ) :
    (RealIsolation.refine b.polynomial b.interval k).width ≤ b.interval.width / (2 : ℚ) ^ k :=
  RealIsolation.refine_width b.brackets k

/-- Characteristic-zero separability and continuity give a genuine rational
bracket for every fixed real algebraic constant. -/
theorem realBracket_exists (a : ℝ) (ha : IsAlgebraic ℚ a) : Nonempty (RealBracket a) := by
  let m := minpoly ℚ a
  have hroot : Polynomial.aeval a m = 0 := minpoly.aeval ℚ a
  have hsep : m.Separable := (minpoly.irreducible ha.isIntegral).separable
  have hd : Polynomial.aeval a m.derivative ≠ 0 := hsep.aeval_derivative_ne_zero hroot
  have oriented : ∃ p : ℚ[X], Polynomial.aeval a p = 0 ∧ 0 < Polynomial.aeval a p.derivative := by
    by_cases hp : 0 < Polynomial.aeval a m.derivative
    · exact ⟨m,hroot,hp⟩
    · refine ⟨-m,by simpa using congrArg Neg.neg hroot,?_⟩
      simpa only [Polynomial.derivative_neg,map_neg] using
        (neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hd))
  obtain ⟨p,hpa,hpd⟩ := oriented
  let U : Set ℝ := {x | 0 < Polynomial.aeval x p.derivative}
  have hU : IsOpen U := isOpen_lt continuous_const p.derivative.continuous_aeval
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hU a hpd
  obtain ⟨l,hl₀,hl₁⟩ := exists_rat_btwn (show a - ε / 2 < a by linarith)
  obtain ⟨u,hu₀,hu₁⟩ := exists_rat_btwn (show a < a + ε / 2 by linarith)
  have hlu : (l : ℝ) < u := hl₁.trans hu₀
  have hmono : StrictMonoOn (fun x : ℝ => Polynomial.aeval x p)
      (Set.Icc (l : ℝ) u) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc _ _) p.continuous_aeval.continuousOn
    intro x hx
    rw [Polynomial.deriv_aeval]
    apply hball
    have hx' := interior_subset hx
    change dist x a < ε
    rw [Real.dist_eq]
    apply abs_lt.mpr
    constructor <;> linarith [hx'.1,hx'.2]
  obtain ⟨code,hcode⟩ :=
    Holant.LocalDrafts.EffectiveAlgebraic.RationalPolynomialCode.exists_code p
  let I : RealInterval := ⟨l,u⟩
  have hac : I.Contains a := ⟨hl₁.le,hu₀.le⟩
  have hlneg : Polynomial.aeval (l : ℝ) p < 0 := by
    have h := hmono ⟨le_rfl,hlu.le⟩ hac hl₁
    simpa only [hpa] using h
  have hupos : 0 < Polynomial.aeval (u : ℝ) p := by
    have h := hmono hac ⟨hlu.le,le_rfl⟩ hu₀
    simpa only [hpa] using h
  have hb : RealIsolation.Brackets code I := by
    refine ⟨?_,?_,?_⟩
    · exact_mod_cast hlu.le
    · have h : (code.evalRational l : ℝ) < 0 := by
        rw [RealIsolation.evalRational_cast,hcode]
        exact hlneg
      exact_mod_cast h.le
    · have h : 0 < (code.evalRational u : ℝ) := by
        rw [RealIsolation.evalRational_cast,hcode]
        exact hupos
      exact_mod_cast h.le
  exact ⟨⟨code,I,hac,by simpa only [hcode] using hpa,hb,
    by simpa only [hcode] using hmono⟩⟩

end
end Paper2.ExactInput.FixedRootCodec
