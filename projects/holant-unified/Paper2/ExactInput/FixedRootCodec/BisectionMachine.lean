import Paper2.ExactInput.FixedRootCodec.BisectionStep
import Paper2.Complexity.BellMachines.BoundedIterateInterface
import Paper2.ExactInput.Bounds.RationalHeight

/-! Polynomial-time fixed-polynomial bisection. The actual common-denominator
state has at most linear bit growth in the round count and its original bits.
The controller consumes a unary round counter, executes every round program,
and charges the intermediate serialization and tape transfers. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines
noncomputable section

theorem bisectionEncoding_length (s : BisectionState) :
    (bisectionEncoding.encode s).length =
      2 * (IntegerArithmetic.encoding.encode s.1).length +
      2 * (IntegerArithmetic.encoding.encode s.2.1).length +
      (encodeNat s.2.2).length + 2 := by
  simp only [bisectionEncoding,pairEncoding_length,encodingNatBool]
  omega

theorem integer_bits_le (z : ℤ) :
    (IntegerArithmetic.encoding.encode z).length ≤ z.natAbs.size + 1 := by
  change (encodeNat (Equiv.intEquivNat z)).length ≤ _
  rw [encodeNat_length]
  exact intCode_size_le z

theorem integer_abs_size_le (z : ℤ) :
    z.natAbs.size ≤ (IntegerArithmetic.encoding.encode z).length + 1 := by
  have h := IntegerArithmetic.magnitudeBits_length_le z
  rw [encodeNat_length] at h
  exact h

/-- The bound is over every intermediate state, including inputs that do not
describe a root bracket. Thus it is a genuine controller bound, not a promise
about only the eventual successfully isolated answer. -/
theorem bisection_prefix_length (p : RationalPolynomialCode) (s : BisectionState) (k : ℕ) :
    (bisectionEncoding.encode ((bisect p)^[k] s)).length ≤
      5 * k + 5 * (bisectionEncoding.encode s).length + 15 := by
  let L := (bisectionEncoding.encode s).length
  let M := max s.1.natAbs s.2.1.natAbs
  have hlen := bisectionEncoding_length s
  have hl : (IntegerArithmetic.encoding.encode s.1).length ≤ L := by omega
  have hu : (IntegerArithmetic.encoding.encode s.2.1).length ≤ L := by omega
  have hq : s.2.2.size ≤ L := by
    rw [← encodeNat_length]
    omega
  have hMl : s.1.natAbs.size ≤ L + 1 := (integer_abs_size_le s.1).trans (by omega)
  have hMu : s.2.1.natAbs.size ≤ L + 1 := (integer_abs_size_le s.2.1).trans (by omega)
  have hM : M.size ≤ L + 1 :=
    Nat.size_le.mpr (max_lt (Nat.size_le.mp hMl) (Nat.size_le.mp hMu))
  have hb := bisection_abs_bound p s M (le_max_left _ _) (le_max_right _ _) k
  have hp := natSize_mul_le (2 ^ k) M
  rw [Nat.size_pow] at hp
  have hleft : (((bisect p)^[k] s).1).natAbs.size ≤ k + L + 2 :=
    (Nat.size_le_size hb.1).trans (hp.trans (by omega))
  have hright : (((bisect p)^[k] s).2.1).natAbs.size ≤ k + L + 2 :=
    (Nat.size_le_size hb.2).trans (hp.trans (by omega))
  have hd : (((bisect p)^[k] s).2.2).size ≤ k + L + 1 := by
    rw [bisection_denominator]
    have h := natSize_mul_le (2 ^ k) s.2.2
    rw [Nat.size_pow] at h
    omega
  have bl := (integer_bits_le (((bisect p)^[k] s).1)).trans
    (Nat.add_le_add_right hleft 1)
  have bu := (integer_bits_le (((bisect p)^[k] s).2.1)).trans
    (Nat.add_le_add_right hright 1)
  rw [bisectionEncoding_length,encodeNat_length]
  omega

def bisectionSpace : Polynomial ℕ := 5 * Polynomial.X + 15

theorem bisection_intermediate (p : RationalPolynomialCode) :
    BellMachines.BoundedIterate.IntermediateBound bisectionEncoding (bisect p) bisectionSpace := by
  intro n s k hk
  have h := bisection_prefix_length p s k
  have hlen :
      ((BellMachines.BoundedIterate.inputEncoding bisectionEncoding).encode (n,s)).length =
        2 * n + 1 + (bisectionEncoding.encode s).length := by
    simp [BellMachines.BoundedIterate.inputEncoding,pairEncoding,
      GraphPreprocessing.UnaryBinary.unaryEncoding]
  simp only [bisectionSpace,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,hlen]
  omega

/-- Actual polynomial-transition bisection, with no arithmetic or output-size
premise left to the caller. Only the fixed polynomial becomes program data. -/
def bisectionComputes (p : RationalPolynomialCode) :
    Computes (BellMachines.BoundedIterate.inputEncoding bisectionEncoding)
      bisectionEncoding (fun x => (bisect p)^[x.1] x.2) :=
  BellMachines.BoundedIterate.computes bisectionEncoding (bisect p)
    (bisectionStepComputes p) bisectionSpace (bisection_intermediate p)

end
end Paper2.ExactInput.FixedRootCodec
