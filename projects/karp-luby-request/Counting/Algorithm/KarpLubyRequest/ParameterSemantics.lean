import Counting.Algorithm.KarpLubyRequest.RationalFields
import Counting.Algorithm.KarpLuby.Program
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Raw parameter contracts for actual unsigned arithmetic calls

R1 rationals use an optional negative predecessor and arbitrary raw natural words.
After the original decoder has checked a nonempty denominator, positivity is
exactly a false sign and a nonempty magnitude. The remaining accuracy checks are
unsigned comparisons. For positive inputs, the reciprocal budget can be computed
by dividing the original denominator by the original magnitude; fraction
normalization does not change this integer quotient. These are value bridges,
not machine-cost assertions.
-/
namespace Counting.Algorithm.KarpLubyRequest.ParameterSemantics
open Computability Counting.Algorithm.KarpLuby

def unsigned (f : RationalFields.Fields) : Prop :=
  f.negative = false ∧ f.magnitude ≠ []

def epsilonValid (f : RationalFields.Fields) : Prop :=
  unsigned f ∧ decodeNat f.magnitude ≤ decodeNat f.denominator

def deltaValid (f : RationalFields.Fields) : Prop :=
  unsigned f ∧ decodeNat f.magnitude < decodeNat f.denominator

lemma denominator_pos (f : RationalFields.Fields) (hd : f.denominator ≠ []) :
    0 < decodeNat f.denominator :=
  Nat.pos_of_ne_zero ((RationalFields.decodeNat_eq_zero_iff f.denominator).not.mpr hd)

lemma value_unsigned (f : RationalFields.Fields) (hs : f.negative = false) :
    RationalFields.value f = (decodeNat f.magnitude : ℚ) / decodeNat f.denominator := by
  simp [RationalFields.value, hs, Rat.mkRat_eq_div]

lemma positive_iff (f : RationalFields.Fields) (hd : f.denominator ≠ []) :
    0 < RationalFields.value f ↔ unsigned f := by
  have hdq : (0 : ℚ) < decodeNat f.denominator := by exact_mod_cast denominator_pos f hd
  cases hs : f.negative with
  | false =>
    rw [value_unsigned f hs, div_pos_iff_of_pos_right hdq]
    simp only [unsigned, hs, true_and]
    have hn : (0 : ℚ) < decodeNat f.magnitude ↔ decodeNat f.magnitude ≠ 0 := by
      exact_mod_cast (Nat.pos_iff_ne_zero : 0 < decodeNat f.magnitude ↔ _)
    rw [hn]
    exact (RationalFields.decodeNat_eq_zero_iff f.magnitude).not
  | true =>
    have hn : RationalFields.value f < 0 := by
      rw [RationalFields.value, if_pos (by exact hs)]
      rw [Rat.mkRat_eq_div]
      apply div_neg_of_neg_of_pos _ hdq
      have hm : (0 : ℚ) ≤ decodeNat f.magnitude := Nat.cast_nonneg _
      simp
      linarith
    simp only [unsigned, hs, Bool.true_eq_false, false_and]
    exact iff_false_intro (not_lt_of_ge hn.le)

lemma epsilonValid_iff (f : RationalFields.Fields) (hd : f.denominator ≠ []) :
    epsilonValid f ↔ 0 < RationalFields.value f ∧ RationalFields.value f ≤ 1 := by
  rw [positive_iff f hd]
  unfold epsilonValid
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    rw [value_unsigned f hu.1]
    apply (div_le_one (by exact_mod_cast denominator_pos f hd : (0 : ℚ) < decodeNat f.denominator)).mpr
    exact_mod_cast hc
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    rw [value_unsigned f hu.1] at hc
    have := (div_le_one (by exact_mod_cast denominator_pos f hd : (0 : ℚ) < decodeNat f.denominator)).mp hc
    exact_mod_cast this

lemma deltaValid_iff (f : RationalFields.Fields) (hd : f.denominator ≠ []) :
    deltaValid f ↔ 0 < RationalFields.value f ∧ RationalFields.value f < 1 := by
  rw [positive_iff f hd]
  unfold deltaValid
  constructor
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    rw [value_unsigned f hu.1]
    apply (div_lt_one (by exact_mod_cast denominator_pos f hd : (0 : ℚ) < decodeNat f.denominator)).mpr
    exact_mod_cast hc
  · rintro ⟨hu, hc⟩
    refine ⟨hu, ?_⟩
    rw [value_unsigned f hu.1] at hc
    have := (div_lt_one (by exact_mod_cast denominator_pos f hd : (0 : ℚ) < decodeNat f.denominator)).mp hc
    exact_mod_cast this

lemma validRequest_iff (e d : RationalFields.Fields)
    (he : e.denominator ≠ []) (hd : d.denominator ≠ []) :
    Program.ValidRequest (RationalFields.value e) (RationalFields.value d) ↔
      epsilonValid e ∧ deltaValid d := by
  rw [epsilonValid_iff e he, deltaValid_iff d hd]
  exact and_assoc.symm

/-- Binary quotient computation may consume the original positive components;
no gcd normalization or loop through the numerical reciprocal is required. -/
theorem reciprocal_raw (f : RationalFields.Fields) (hd : f.denominator ≠ []) (hu : unsigned f) :
    reciprocalCeiling (RationalFields.value f) =
      decodeNat f.denominator / decodeNat f.magnitude + 1 := by
  have hp := (positive_iff f hd).mpr hu
  have hr : (decodeNat f.denominator : ℚ) / decodeNat f.magnitude =
      (RationalFields.value f).den / (RationalFields.value f).num.toNat := by
    calc
      (decodeNat f.denominator : ℚ) / decodeNat f.magnitude =
          1 / ((decodeNat f.magnitude : ℚ) / decodeNat f.denominator) := by simp
      _ = 1 / RationalFields.value f := by rw [value_unsigned f hu.1]
      _ = (RationalFields.value f).den / (RationalFields.value f).num.toNat := by
        conv_lhs => rw [positive_rat_eq_num_toNat_div_den hp]
        simp
  have hfloor := congrArg (fun q : ℚ => Nat.floor q) hr
  simp only [Nat.floor_div_natCast, Nat.floor_natCast] at hfloor
  unfold reciprocalCeiling
  omega

end Counting.Algorithm.KarpLubyRequest.ParameterSemantics
