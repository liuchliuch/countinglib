import Counting.Algorithm.KarpLuby.ResourceBounds
import Counting.Algorithm.KarpLuby.ProgramEncoding

/-! Resource bounds in the bit length of the concrete explicit-DNF encoding. -/
namespace Counting.Algorithm.KarpLuby

open DNF
variable {n : ℕ}

/-- The concrete input length charges both all variables and all term occurrences. -/
def formulaBitLength (f : Formula n) : ℕ := (Encoding.encodeInput ⟨n, f⟩).length

private theorem size_le_value (v : ℕ) : v.size ≤ v :=
  Nat.size_le.mpr Nat.lt_two_pow_self

/-- A polynomial bound on the actual random tape in the encoded DNF size. -/
theorem requestedBudget_le_formula_bits (f : Formula n) (epsilon delta : ℚ) :
    Program.requestedBudget f epsilon delta ≤
      288 * (delta.den.size + 2) * formulaBitLength f *
        reciprocalCeiling epsilon ^ 2 * (2 * formulaBitLength f + 1) := by
  have hm : f.length ≤ formulaBitLength f := Encoding.terms_le_input_length ⟨n, f⟩
  have hn : n ≤ formulaBitLength f := Encoding.variables_le_input_length ⟨n, f⟩
  have hs : f.length.size ≤ formulaBitLength f := (size_le_value _).trans hm
  calc
    _ ≤ 2 * (delta.den.size + 2) *
        (144 * f.length * reciprocalCeiling epsilon ^ 2 * (f.length.size + n + 1)) :=
      ResourceBounds.requestedBudget_le_raw f epsilon delta
    _ ≤ 2 * (delta.den.size + 2) *
        (144 * formulaBitLength f * reciprocalCeiling epsilon ^ 2 *
          (formulaBitLength f + formulaBitLength f + 1)) := by gcongr
    _ = _ := by ring

/-- The requested tape grows polynomially in input bits and inverse accuracy. -/
theorem requestedBudget_le_formula_bits_inverse (f : Formula n) {epsilon : ℚ}
    (he : 0 < epsilon) (delta : ℚ) :
    (Program.requestedBudget f epsilon delta : ℚ) ≤
      288 * (delta.den.size + 2 : ℚ) * (formulaBitLength f : ℚ) *
        (1 / epsilon + 1)^2 * (2 * (formulaBitLength f : ℚ) + 1) := by
  have h : (Program.requestedBudget f epsilon delta : ℚ) ≤
      288 * (delta.den.size + 2 : ℚ) * (formulaBitLength f : ℚ) *
        (reciprocalCeiling epsilon : ℚ)^2 * (2 * (formulaBitLength f : ℚ) + 1) := by
    exact_mod_cast requestedBudget_le_formula_bits f epsilon delta
  refine h.trans ?_
  have hc := reciprocalCeiling_le_inv_add_one he
  gcongr

/-- The actual framed binary output length, not only a rational magnitude bound. -/
theorem runEncoded_length_le (f : Formula n) (epsilon delta : ℚ)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    (Program.runEncoded f epsilon delta tape).length ≤
      7 * formulaBitLength f + 6 * epsilon.den.size + 42 := by
  have hcode := Encoding.output_length_le (Program.run f epsilon delta tape)
  obtain ⟨hnum, hden⟩ := ResourceBounds.run_output_size_le f epsilon delta tape
  have hm : f.length ≤ formulaBitLength f := Encoding.terms_le_input_length ⟨n, f⟩
  have hn : n ≤ formulaBitLength f := Encoding.variables_le_input_length ⟨n, f⟩
  have hs : f.length.size ≤ formulaBitLength f := (size_le_value _).trans hm
  change (Program.run f epsilon delta tape).num.natAbs.size ≤ _ at hnum
  change (Program.run f epsilon delta tape).den.size ≤ _ at hden
  change (Encoding.encodeOutput (Program.run f epsilon delta tape)).length ≤ _
  omega

end Counting.Algorithm.KarpLuby
