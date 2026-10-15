import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Stages

/-! # The actual canonical adder consumes accumulator and trial numerator -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
open Turing Computability Holant.Complexity StackProtocol

set_option backward.isDefEq.respectTransparency false

def additionTime (a b : ℕ) : ℕ :=
  max (encodeNat a).length (encodeNat b).length + (encodeNat (a + b)).length + 2

theorem addition_exact (rows mass suffix : List Bool) (a b : ℕ) :
    RunsExactly computer.step
      (config (.add false) (ready rows mass suffix (encodeNat a) (encodeNat b)))
      (config (.move 0) (summed rows mass suffix (encodeNat (a + b))))
      (additionTime a b) := by
  apply MachineCall.run additionStacks Label.add (.move 0) additionState
    BinaryArithmetic.Addition.program program addition_code (none, false)
    (ready rows mass suffix [] [])
    (BinaryArithmetic.Addition.cfg (some false) false (encodeNat a) (encodeNat b) [] [])
    (BinaryArithmetic.Addition.cfg none false [] [] [] (encodeNat (a + b)))
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; cases k <;> rfl
    · intro k hk
      cases k with
      | inl k =>
        cases k <;> first | rfl | exact False.elim (hk .right rfl)
      | inr k =>
        fin_cases k <;> first
        | rfl
        | exact False.elim (hk .left rfl)
        | exact False.elim (hk .work rfl)
        | exact False.elim (hk .out rfl)
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; cases k <;> rfl
    · intro k hk
      cases k with
      | inl k => cases k <;> rfl
      | inr k =>
        fin_cases k <;> first
        | rfl
        | exact False.elim (hk .left rfl)
        | exact False.elim (hk .work rfl)
        | exact False.elim (hk .out rfl)
  · exact BinaryArithmetic.Addition.compute_encodeNat_exact a b

theorem sum_length_le (a b : ℕ) :
    (encodeNat (a + b)).length ≤ max (encodeNat a).length (encodeNat b).length + 1 := by
  simpa only [BinaryArithmetic.addBits_encodeNat] using
    BinaryArithmetic.addBits_length_le false (encodeNat a) (encodeNat b)

theorem additionTime_le (a b : ℕ) :
    additionTime a b ≤ 2 * max (encodeNat a).length (encodeNat b).length + 3 := by
  have h := sum_length_le a b
  unfold additionTime
  omega

end Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
