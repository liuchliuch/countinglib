import Counting.Algorithm.KarpLubyRequest.Contract
import Counting.Algorithm.KarpLubyMachine.FractionNormalization

/-! Literal nonnegative rational output, including the zero-denominator convention.
These specifications are separate from the finite serializer in `Program`. -/
namespace Counting.Algorithm.KarpLubyRequest.Output
open Computability Holant.Complexity
open Counting.Algorithm.KarpLuby

/-- Natural numerator after exact rational reduction. -/
def numerator (a s : ℕ) : ℕ := if s = 0 then 0 else a / Nat.gcd a s
/-- A zero denominator is normalized to one, as in `mkRat`. -/
def denominator (a s : ℕ) : ℕ := if s = 0 then 1 else s / Nat.gcd a s

theorem quotient_eq (a s : ℕ) : (a : ℚ) / s = mkRat (a : ℤ) s := by
  simp only [Rat.mkRat_eq_div, Int.cast_natCast]

theorem quotient_num (a s : ℕ) : ((a : ℚ) / s).num = (numerator a s : ℤ) := by
  rw [quotient_eq]
  by_cases hs : s = 0
  · subst s
    rfl
  · have h := RationalArithmetic.mkRat_num_ofSign false a s hs
    change (mkRat (a : ℤ) s).num = ((a / Nat.gcd a s : ℕ) : ℤ) at h
    simpa only [numerator, hs, ite_false] using h

theorem quotient_den (a s : ℕ) : ((a : ℚ) / s).den = denominator a s := by
  rw [quotient_eq]
  by_cases hs : s = 0
  · subst s
    rfl
  · have h := RationalArithmetic.mkRat_den_ofSign false a s hs
    change (mkRat (a : ℤ) s).den = s / Nat.gcd a s at h
    simpa only [denominator, hs, ite_false] using h

/-- The canonical H1 integer code for a nonnegative numerator. -/
def parityWord (n : ℕ) : List Bool := IntegerArithmetic.encoding.encode (n : ℤ)

theorem parityWord_tail (n : ℕ) : (parityWord n).tail = encodeNat n := by
  exact IntegerArithmetic.encoding_tail (n : ℤ)

theorem parityWord_eq (n : ℕ) :
    parityWord n = IntegerArithmetic.recode false (encodeNat n) := by
  exact (IntegerArithmetic.recode_encodeNat false n).symm

theorem parityWord_length (n : ℕ) : (parityWord n).length ≤ (encodeNat n).length + 1 := by
  rw [parityWord_eq]
  exact RationalArithmetic.Normalization.recode_length_le false _

theorem normalized_components (a s : ℕ) :
    RationalArithmetic.normalizeBits false (encodeNat a) (encodeNat s) =
      (parityWord (numerator a s), encodeNat (denominator a s)) := by
  rw [RationalArithmetic.normalizeBits_encodeNat]
  change (IntegerArithmetic.encoding.encode (mkRat (a : ℤ) s).num,
    encodeNat (mkRat (a : ℤ) s).den) = _
  rw [← quotient_eq, quotient_num, quotient_den]
  rfl

/-- The original literal natural-pair codec used for the internal output stage. -/
def input (a s : ℕ) : List Bool := (Encoding.prod Encoding.nat Encoding.nat).encode (a, s)
theorem input_eq (a s : ℕ) : input a s = Encoding.frame (encodeNat a) ++ encodeNat s := rfl

theorem input_length (a s : ℕ) :
    (input a s).length = 2 * (encodeNat a).length + (encodeNat s).length + 1 := by
  rw [input_eq, List.length_append, Encoding.frame_length]
  omega

/-- The six escaped bits of the positive-integer tag. The denominator is an
unframed suffix, exactly as required by `Encoding.prod`. -/
def signPrefix : List Bool := [true, true, true, false, true, false]

theorem encode_nonnegative (q : ℚ) (n : ℕ) (h : q.num = (n : ℤ)) :
    Encoding.encodeOutput q = signPrefix ++ Encoding.frame (encodeNat n) ++ encodeNat q.den := by
  change Encoding.frame (Encoding.int.encode q.num) ++ encodeNat q.den = _
  rw [h]
  rfl

theorem output_eq (a s : ℕ) :
    Encoding.encodeOutput ((a : ℚ) / s) =
      signPrefix ++ Encoding.frame (encodeNat (numerator a s)) ++ encodeNat (denominator a s) := by
  rw [encode_nonnegative _ _ (quotient_num a s), quotient_den]

theorem numerator_length_le (a s : ℕ) :
    (encodeNat (numerator a s)).length ≤ (encodeNat a).length := by
  by_cases hs : s = 0
  · simp only [numerator, hs, ite_true]
    exact Nat.zero_le _
  · simpa only [numerator, hs, ite_false] using
      RationalArithmetic.Normalization.quotient_length_le a (Nat.gcd a s)

theorem denominator_length_le (a s : ℕ) :
    (encodeNat (denominator a s)).length ≤ (encodeNat s).length + 1 := by
  by_cases hs : s = 0
  · subst s
    simp only [denominator, ite_true]
    decide
  · have h := RationalArithmetic.Normalization.quotient_length_le s (Nat.gcd a s)
    simpa only [denominator, hs, ite_false] using h.trans (Nat.le_add_right _ 1)

end Counting.Algorithm.KarpLubyRequest.Output
