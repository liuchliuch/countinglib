import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Bounds
import Counting.Algorithm.KarpLubyRequest.Median.Machine
import Counting.Algorithm.KarpLubyRequest.Output.Machine

/-!
# Polynomial substitution for the actual evaluator's component bounds

The positive tape-budget gate supplies bounds on the numeric sample and group
counts, separately from their binary lengths. This module substitutes a common
physical bound into the existing nested-loop, median and output expressions.
It does not assume or assert a whole-request execution theorem, and it does not
charge transfers between these components on their behalf.
-/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation.LengthBounds
open Computability
open Sampling
open Polynomial

def groupBound (N : ℕ) : ℕ := 1980 * N ^ 3 + 1380 * N ^ 2 + 314 * N + 47
def orbitBound (N : ℕ) : ℕ := 8 * N ^ 2 + 13 * N + 4
def outerBound (N : ℕ) : ℕ := 1980 * N ^ 4 + 1396 * N ^ 3 + 342 * N ^ 2 + 60 * N + 1
def medianInputBound (N : ℕ) : ℕ := 4 * N ^ 2 + 5 * N + 1

/-- Both counts here are numeric iteration counts; `sampleBits` is separate. -/
theorem group_time_le (rows width sampleBits samples groups tape N : ℕ)
    (hr : rows ≤ N) (hw : width ≤ N) (ha : sampleBits ≤ N)
    (hs : samples ≤ N) (hg : groups ≤ N) (ht : tape ≤ N) :
    GroupBody.timeBound rows width sampleBits
      (groups * (2 * sampleBits + 2 * width + 3)) tape samples ≤ groupBound N := by
  calc
    _ ≤ GroupBody.timeBound N N N (N * (2 * N + 2 * N + 3)) N N := by
      unfold GroupBody.timeBound
      gcongr
    _ = groupBound N := by unfold GroupBody.timeBound groupBound; ring

theorem orbit_word_le (rows width sampleBits groups tape N : ℕ)
    (hr : rows ≤ N) (hw : width ≤ N) (ha : sampleBits ≤ N)
    (hg : groups ≤ N) (ht : tape ≤ N) :
    GroupBody.orbitWordBound rows width sampleBits tape groups ≤ orbitBound N := by
  calc
    _ ≤ GroupBody.orbitWordBound N N N N N := by
      unfold GroupBody.orbitWordBound
      gcongr
    _ = orbitBound N := by unfold GroupBody.orbitWordBound orbitBound; ring

/-- Includes outer countdown, body calls, every output copy and final zero test,
exactly as in the previously proved iteration-bound expression. -/
theorem outer_time_le (rows width sampleBits samples groups groupBits tape N : ℕ)
    (hr : rows ≤ N) (hw : width ≤ N) (ha : sampleBits ≤ N)
    (hs : samples ≤ N) (hg : groups ≤ N) (hb : groupBits ≤ N) (ht : tape ≤ N) :
    1 + groups *
      (GroupBody.timeBound rows width sampleBits
          (groups * (2 * sampleBits + 2 * width + 3)) tape samples +
        2 * (GroupBody.orbitWordBound rows width sampleBits tape groups + 1) +
        2 * groupBits + 3) ≤ outerBound N := by
  have hbody := group_time_le rows width sampleBits samples groups tape N hr hw ha hs hg ht
  have hword := orbit_word_le rows width sampleBits groups tape N hr hw ha hg ht
  calc
    _ ≤ 1 + N * (groupBound N + 2 * (orbitBound N + 1) + 2 * N + 3) := by gcongr
    _ = outerBound N := by unfold groupBound orbitBound outerBound; ring

noncomputable def outerPolynomial : Polynomial ℕ :=
  C 1980 * X ^ 4 + C 1396 * X ^ 3 + C 342 * X ^ 2 + C 60 * X + C 1

@[simp] theorem outerPolynomial_eval (N : ℕ) : outerPolynomial.eval N = outerBound N := by
  simp [outerPolynomial, outerBound]

/-- The statement budget is the concrete body machine's syntactic budget.
The enclosing iteration adds eight, as in its actual Primitive theorem. -/
noncomputable def primitivePolynomial (bodyBudget : ℕ) : Polynomial ℕ :=
  C (8 + bodyBudget) * outerPolynomial

@[simp] theorem primitivePolynomial_eval (bodyBudget N : ℕ) :
    (primitivePolynomial bodyBudget).eval N = (8 + bodyBudget) * outerBound N := by
  simp [primitivePolynomial]

theorem outer_primitive_le (bodyBudget rows width sampleBits samples groups groupBits tape N : ℕ)
    (hr : rows ≤ N) (hw : width ≤ N) (ha : sampleBits ≤ N)
    (hs : samples ≤ N) (hg : groups ≤ N) (hb : groupBits ≤ N) (ht : tape ≤ N) :
    (8 + bodyBudget) * (1 + groups *
      (GroupBody.timeBound rows width sampleBits
          (groups * (2 * sampleBits + 2 * width + 3)) tape samples +
        2 * (GroupBody.orbitWordBound rows width sampleBits tape groups + 1) +
        2 * groupBits + 3)) ≤ (primitivePolynomial bodyBudget).eval N := by
  rw [primitivePolynomial_eval]
  exact Nat.mul_le_mul_left _
    (outer_time_le rows width sampleBits samples groups groupBits tape N hr hw ha hs hg hb ht)

theorem median_serialized_le (groups groupBits sampleBits width N : ℕ)
    (hg : groups ≤ N) (hb : groupBits ≤ N) (ha : sampleBits ≤ N) (hw : width ≤ N) :
    2 * groupBits + groups * (2 * (sampleBits + width + 1) + 1) + 1 ≤ medianInputBound N := by
  calc
    _ ≤ 2 * N + N * (2 * (N + N + 1) + 1) + 1 := by gcongr
    _ = medianInputBound N := by unfold medianInputBound; ring

/-- The bound applies to the literal existing natural-list codec. -/
theorem median_input_le (groups : ℕ) (z : Fin groups → ℕ) (sampleBits width N : ℕ)
    (hg : groups ≤ N) (hb : (encodeNat groups).length ≤ N)
    (ha : sampleBits ≤ N) (hw : width ≤ N)
    (hz : ∀ i, (encodeNat (z i)).length ≤ sampleBits + width + 1) :
    (Median.input (List.ofFn z)).length ≤ medianInputBound N :=
  (Median.input_ofFn_length_le groups z (sampleBits + width + 1) hz).trans
    (median_serialized_le groups (encodeNat groups).length sampleBits width N hg hb ha hw)

noncomputable def medianPolynomial : Polynomial ℕ :=
  C 100 * (C 4 * X ^ 2 + C 5 * X + C 2) ^ 3

@[simp] theorem medianPolynomial_eval (N : ℕ) :
    medianPolynomial.eval N = 100 * (medianInputBound N + 1) ^ 3 := by
  simp [medianPolynomial, medianInputBound]

theorem median_time_le (length N : ℕ) (h : length ≤ medianInputBound N) :
    Median.timeBound length ≤ medianPolynomial.eval N := by
  rw [medianPolynomial_eval]
  exact Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 3)

/-- The selected natural numerator needs at most sampleBits + width + 1 bits;
the sample denominator itself needs sampleBits bits, even if its value is large. -/
theorem output_input_le (numerator samples sampleBits width N : ℕ)
    (ha : sampleBits ≤ N) (hw : width ≤ N)
    (hn : (encodeNat numerator).length ≤ sampleBits + width + 1)
    (hs : (encodeNat samples).length ≤ sampleBits) :
    (Output.input numerator samples).length ≤ 5 * N + 3 := by
  rw [Output.input_length]
  omega

noncomputable def outputPolynomial : Polynomial ℕ := C 200 * (C 5 * X + C 4) ^ 3

@[simp] theorem outputPolynomial_eval (N : ℕ) :
    outputPolynomial.eval N = 200 * (5 * N + 4) ^ 3 := by
  simp [outputPolynomial]

theorem output_timeBound_le (length N : ℕ) (h : length ≤ 5 * N + 3) :
    Output.timeBound length ≤ outputPolynomial.eval N := by
  rw [outputPolynomial_eval]
  apply Nat.mul_le_mul_left 200
  exact Nat.pow_le_pow_left (by omega) 3

/-- The same bound applies when normalization is called on its component bank. -/
theorem output_componentTime_le (numerator samples sampleBits width N : ℕ)
    (ha : sampleBits ≤ N) (hw : width ≤ N)
    (hn : (encodeNat numerator).length ≤ sampleBits + width + 1)
    (hs : (encodeNat samples).length ≤ sampleBits) :
    Output.componentTime numerator samples ≤ outputPolynomial.eval N :=
  (Output.componentTime_le numerator samples).trans
    (output_timeBound_le _ N (output_input_le numerator samples sampleBits width N ha hw hn hs))

end Counting.Algorithm.KarpLubyRequest.Evaluation.LengthBounds
