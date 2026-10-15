import Counting.Algorithm.KarpLubyRequest.Sampling.TrialSelection
import Counting.Algorithm.KarpLubyRequest.Sampling.TrialFinish
import Counting.Algorithm.KarpLubyRequest.Sampling.TrialSpec
import Counting.Algorithm.KarpLubyRequest.Sampling.TrialBudget

/-! # Connected selection, ownership, scaling, and cleanup control flow -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Trial
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing

set_option backward.isDefEq.respectTransparency false

theorem selected_true (d : Data) :
    computer.step (configuration .selected (selectedState true) d) =
      some (configuration (.unrank 0) initial d) := rfl

theorem selected_false (d : Data) :
    computer.step (configuration .selected (selectedState false) d) =
      some (configuration (.clear 0) initial d) := rfl

theorem owner_start (d : Data) :
    computer.step (configuration .ownerStart initial d) =
      some (configuration (.owner 0) (ownedState true) d) := rfl

theorem owned_true (d : Data) :
    computer.step (configuration .owned (ownedState true) d) =
      some (configuration .scaleMove initial d) := rfl

theorem owned_false (d : Data) :
    computer.step (configuration .owned (ownedState false) d) =
      some (configuration (.clear 0) initial d) := rfl

def value (mass : List Bool) (q : SelectorSpec.Result) : ℕ :=
  if q.selected && Owner.answer q.prior (RowSemantics.sample q.row q.rank)
    then 2 ^ mass.length else 0

def scaledData (rows mass suffix : List Bool) (q : SelectorSpec.Result) : Data :=
  {(ownedData rows mass suffix q) with clock := [], output := encodeNat (2 ^ mass.length)}

def afterTime (rows mass suffix : List Bool) (q : SelectorSpec.Result) : ℕ :=
  if q.selected then
    1 + (2 * q.row.length + 3) + 1 + Owner.runTime q.prior (RowSemantics.sample q.row q.rank) + 1 +
      if Owner.answer q.prior (RowSemantics.sample q.row q.rank) then
        3 * mass.length + 4 + cleanupTime (scaledData rows mass suffix q)
      else cleanupTime (ownedData rows mass suffix q)
  else 1 + cleanupTime (selectedData rows mass suffix q)

/-- Every branch ends with a clean bank. False selection and failed ownership
actually jump to cleanup, and never execute the dyadic-output constructor. -/
theorem after_selection (rows mass suffix : List Bool) (q : SelectorSpec.Result)
    (hlen : q.selected = true → ∀ row ∈ q.prior, row.length = q.row.length) :
    RunsExactly computer.step
      (configuration .selected (selectedState q.selected) (selectedData rows mass suffix q))
      (finalConfiguration rows mass suffix (encodeNat (value mass q)))
      (afterTime rows mass suffix q) := by
  have hz : encodeNat 0 = ([] : List Bool) := rfl
  cases hs : q.selected with
  | false =>
    have h := (runsExactly_one (selected_false (selectedData rows mass suffix q))).trans
      (cleanup_exact (selectedData rows mass suffix q))
    simpa only [hs, afterTime, Bool.false_eq_true, ↓reduceIte, value, Bool.false_and,
      selectedData, inputData, hz, Nat.add_comm] using h
  | true =>
    have h1 := runsExactly_one (selected_true (selectedData rows mass suffix q))
    have h2 := unrank_call rows mass suffix q
    have h3 := runsExactly_one (owner_start (sampledData rows mass suffix q))
    have h4 := owner_call rows mass suffix q (hlen hs)
    have first := ((h1.trans h2).trans h3).trans h4
    cases ha : Owner.answer q.prior (RowSemantics.sample q.row q.rank) with
    | false =>
      rw [ha] at first
      have h5 := runsExactly_one (owned_false (ownedData rows mass suffix q))
      have h6 := cleanup_exact (ownedData rows mass suffix q)
      have h := (first.trans h5).trans h6
      simpa only [hs, afterTime, ha, Bool.false_eq_true, ↓reduceIte, value, Bool.true_and,
        ownedData, sampledData, selectedData, inputData, hz,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    | true =>
      rw [ha] at first
      have h5 := runsExactly_one (owned_true (ownedData rows mass suffix q))
      have h6 := scale_output (ownedData rows mass suffix q) rfl rfl rfl
      have h7 := cleanup_exact (scaledData rows mass suffix q)
      have h := ((first.trans h5).trans h6).trans h7
      simpa only [hs, afterTime, ha, ↓reduceIte, value, Bool.true_and,
        scaledData, ownedData, sampledData, selectedData, inputData,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def selectedTime (rows : List RowSemantics.Cells) (mass suffix : List Bool) (r : ℕ) : ℕ :=
  Selector.runTime rows r + afterTime (Dense.CellCodec.rows rows) mass suffix (SelectorSpec.seek rows r [])

theorem select_to_halt (n : ℕ) (rows : List RowSemantics.Cells) (mass suffix : List Bool) (r : ℕ)
    (hlen : ∀ row ∈ rows, row.length = n) :
    RunsExactly computer.step
      (configuration (.selector 0) initial (selectionData (Dense.CellCodec.rows rows) mass suffix r))
      (finalConfiguration (Dense.CellCodec.rows rows) mass suffix (encodeNat (value mass (SelectorSpec.seek rows r []))))
      (selectedTime rows mass suffix r) := by
  have h1 := selector_call rows mass suffix r
  have h2 := after_selection (Dense.CellCodec.rows rows) mass suffix (SelectorSpec.seek rows r [])
    (by
      intro hs row hm
      have hr := TrialSpec.selected_prior_length n rows r hlen hs row hm
      have hq := SelectorSpec.selected_row_length n rows r [] hlen hs
      exact hr.trans hq.symm)
  convert h1.trans h2 using 1 <;> dsimp [selectedTime] <;> omega

end Counting.Algorithm.KarpLubyRequest.Sampling.Trial
