import Counting.Algorithm.KarpLubyRequest.Evaluation.Run
import Counting.Algorithm.KarpLubyRequest.Evaluation.LengthBounds

/-!
# Polynomial cost of the actual prepared evaluator

This bound substitutes physical lengths and numeric iteration counts into the
time of the single program proved in `Run`. Parsing, transfers, list framing,
the two loops, median selection, fraction normalization and cleanup are charged.
The raw-request preparation stage must establish the bounds below; binary
counter lengths alone do not bound the number of iterations.
-/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
open Computability Polynomial
open Counting.Algorithm.KarpLubyMachine
open Sampling

theorem result_bits_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hrows : ∀ row ∈ rows, row.length = n) (s g : ℕ) (tape : List Bool) :
    ∀ a ∈ (groupResult n rows s g tape).1,
      (encodeNat a).length ≤ (encodeNat s).length +
        (encodeNat (TotalMass.rowSum rows)).length + 1 :=
  TapeBounds.group_numerator_bits_le _ s _ g [] tape
    (SampleBody.width_original n rows hrows) (by simp)

/-- Selection returns an observed numerator, with zero for the empty list. -/
theorem median_bits_le (xs : List ℕ) (bits : ℕ)
    (h : ∀ a ∈ xs, (encodeNat a).length ≤ bits) :
    (encodeNat (Median.value xs)).length ≤ bits := by
  by_cases he : xs = []
  · subst xs
    change 0 ≤ bits
    exact Nat.zero_le bits
  · have hg : 0 < xs.length := List.length_pos_iff.mpr he
    obtain ⟨i, hi⟩ := NumeratorMedian.median_observed xs.length xs.get hg
    have hv := Median.value_ofFn xs.length xs.get
    rw [List.ofFn_get] at hv
    rw [hv, hi]
    exact h _ (List.get_mem xs i)

theorem outerTime_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hrows : ∀ row ∈ rows, row.length = n) (s g : ℕ) (tape : List Bool) (N : ℕ)
    (hr : (Dense.CellCodec.rows rows).length ≤ N)
    (hw : (encodeNat (TotalMass.rowSum rows)).length ≤ N)
    (ha : (encodeNat s).length ≤ N) (hs : s ≤ N) (hg : g ≤ N)
    (hb : (encodeNat g).length ≤ N) (ht : tape.length ≤ N) :
    outerTime n rows s g tape ≤ LengthBounds.outerBound N := by
  apply le_trans (Iteration.ticks_le _ _ _ g _ _ _ ?_ ?_)
    (LengthBounds.outer_time_le _ _ _ _ _ _ _ N hr hw ha hs hg hb ht)
  · intro i hi
    exact GroupBody.sourceTime_on_le n rows hrows s g tape i (by omega)
  · intro i hi
    exact GroupBody.state_word_on_le n rows hrows s g tape (i + 1) (by omega)

theorem result_median_input_le (n : ℕ) (rows : List RowSemantics.Cells)
    (hrows : ∀ row ∈ rows, row.length = n) (s g : ℕ) (tape : List Bool) (N : ℕ)
    (hw : (encodeNat (TotalMass.rowSum rows)).length ≤ N)
    (ha : (encodeNat s).length ≤ N) (hg : g ≤ N)
    (hb : (encodeNat g).length ≤ N) :
    (Median.input (groupResult n rows s g tape).1).length ≤
      LengthBounds.medianInputBound N := by
  let xs := (groupResult n rows s g tape).1
  have hx : xs.length = g := result_length n rows s g tape
  have h := LengthBounds.median_input_le xs.length xs.get
    (encodeNat s).length (encodeNat (TotalMass.rowSum rows)).length N
    (by simpa only [hx] using hg) (by simpa only [hx] using hb) ha hw
    (fun i => result_bits_le n rows hrows s g tape _ (List.get_mem xs i))
  simpa only [List.ofFn_get] using h

/-- A fixed polynomial for the actual evaluator, independent of the request. -/
noncomputable def costPolynomial : Polynomial ℕ :=
  LengthBounds.outerPolynomial + LengthBounds.medianPolynomial +
    LengthBounds.outputPolynomial + C 12 * X ^ 2 + C 41 * X + C 45

@[simp] theorem costPolynomial_eval (N : ℕ) :
    costPolynomial.eval N = LengthBounds.outerBound N +
      LengthBounds.medianPolynomial.eval N + LengthBounds.outputPolynomial.eval N +
      12 * N ^ 2 + 41 * N + 45 := by
  simp only [costPolynomial, eval_add, eval_mul, eval_C, eval_pow, eval_X,
    LengthBounds.outerPolynomial_eval]

/-- Every term is from the actual `timeBound`, including all inter-component
transfers and final cleanup. Numeric counts and their lengths are separate. -/
theorem timeBound_le_polynomial (n : ℕ) (rows : List RowSemantics.Cells)
    (hrows : ∀ row ∈ rows, row.length = n) (s g : ℕ) (tape : List Bool) (N : ℕ)
    (hr : (Dense.CellCodec.rows rows).length ≤ N)
    (hw : (encodeNat (TotalMass.rowSum rows)).length ≤ N)
    (ha : (encodeNat s).length ≤ N) (hs : s ≤ N) (hg : g ≤ N)
    (hb : (encodeNat g).length ≤ N) (ht : tape.length ≤ N) :
    timeBound n rows s g tape ≤ costPolynomial.eval N := by
  let xs := (groupResult n rows s g tape).1
  have hbits := result_bits_le n rows hrows s g tape
  have hselected := median_bits_le xs _ hbits
  have hhistory := GroupBody.reversed_length_le xs _ hbits
  have hlength : xs.length = g := result_length n rows s g tape
  rw [hlength] at hhistory
  have hhistory' : (GroupOutput.reversed xs).length ≤ N * (4 * N + 3) := by
    apply hhistory.trans
    calc
      _ ≤ N * (2 * (N + N + 1) + 1) := by gcongr
      _ = _ := by ring
  have houter := outerTime_le n rows hrows s g tape N hr hw ha hs hg hb ht
  have hinput := result_median_input_le n rows hrows s g tape N hw ha hg hb
  have hmedian := LengthBounds.median_time_le _ N hinput
  have houtput := LengthBounds.output_componentTime_le (Median.value xs) s
    (encodeNat s).length (encodeNat (TotalMass.rowSum rows)).length N ha hw hselected le_rfl
  rw [costPolynomial_eval]
  unfold timeBound groupPhaseTime tailTime
  dsimp only
  change (encodeNat (Median.value (groupResult n rows s g tape).1)).length ≤ _ at hselected
  change (GroupOutput.reversed (groupResult n rows s g tape).1).length ≤ _ at hhistory'
  change Output.componentTime (Median.value (groupResult n rows s g tape).1) s ≤ _ at houtput
  unfold LengthBounds.medianInputBound at hinput
  nlinarith

/-- Primitive interpreter cost uses this same finite program's fixed budget. -/
noncomputable def primitiveCostPolynomial : Polynomial ℕ :=
  C machine.primitiveBudget * costPolynomial

theorem primitive_timeBound_le_polynomial (n : ℕ) (rows : List RowSemantics.Cells)
    (hrows : ∀ row ∈ rows, row.length = n) (s g : ℕ) (tape : List Bool) (N : ℕ)
    (hr : (Dense.CellCodec.rows rows).length ≤ N)
    (hw : (encodeNat (TotalMass.rowSum rows)).length ≤ N)
    (ha : (encodeNat s).length ≤ N) (hs : s ≤ N) (hg : g ≤ N)
    (hb : (encodeNat g).length ≤ N) (ht : tape.length ≤ N) :
    machine.primitiveBudget * timeBound n rows s g tape ≤ primitiveCostPolynomial.eval N := by
  simp only [primitiveCostPolynomial, eval_mul, eval_C]
  exact Nat.mul_le_mul_left _ (timeBound_le_polynomial n rows hrows s g tape N hr hw ha hs hg hb ht)

end Counting.Algorithm.KarpLubyRequest.Evaluation
