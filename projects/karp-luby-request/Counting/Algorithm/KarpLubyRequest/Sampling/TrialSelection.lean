import Counting.Algorithm.KarpLubyRequest.Sampling.TrialBank

/-! # Actual selector, unranker, and ownership calls in the trial bank -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Trial
open Turing Computability Holant.Complexity StackProtocol

def selectedData (rows mass suffix : List Bool) (q : SelectorSpec.Result) : Data :=
  {(inputData rows mass suffix) with
    remaining := Dense.CellCodec.rows q.remaining
    rank := encodeNat q.rank
    row := Dense.CellCodec.encode q.row
    rowMass := if q.selected then encodeNat (2 ^ RowSemantics.free q.row) else []
    history := Dense.CellCodec.rows q.prior}

def selectedState (selected : Bool) : State := (none, none, none, selected, false)

theorem selector_call (rows : List RowSemantics.Cells) (mass suffix : List Bool) (rank : ℕ) :
    RunsExactly computer.step
      (configuration (.selector 0) initial
        (selectionData (Dense.CellCodec.rows rows) mass suffix rank))
      (configuration .selected (selectedState (SelectorSpec.seek rows rank []).selected)
        (selectedData (Dense.CellCodec.rows rows) mass suffix (SelectorSpec.seek rows rank [])))
      (Selector.runTime rows rank) := by
  apply MachineCall.run selectorStacks Label.selector .selected selectorState
    Selector.program program selector_code false
    (inputData (Dense.CellCodec.rows rows) mass suffix).tapes
    (Selector.config 0 (Dense.CellCodec.rows rows) (encodeNat rank) [] [] [] [] [] [] [] [] [])
    (Selector.resultCfg (SelectorSpec.seek rows rank []))
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro j h; cases j <;> first
        | rfl
        | exact (h 0 rfl).elim
        | exact (h 1 rfl).elim
        | exact (h 2 rfl).elim
        | exact (h 3 rfl).elim
        | exact (h 4 rfl).elim
        | exact (h 5 rfl).elim
        | exact (h 6 rfl).elim
        | exact (h 7 rfl).elim
        | exact (h 8 rfl).elim
        | exact (h 9 rfl).elim
        | exact (h 10 rfl).elim
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro j h; cases j <;> first
        | rfl
        | exact (h 0 rfl).elim
        | exact (h 1 rfl).elim
        | exact (h 2 rfl).elim
        | exact (h 3 rfl).elim
        | exact (h 4 rfl).elim
        | exact (h 5 rfl).elim
        | exact (h 6 rfl).elim
        | exact (h 7 rfl).elim
        | exact (h 8 rfl).elim
        | exact (h 9 rfl).elim
        | exact (h 10 rfl).elim
  · exact Selector.run_exact rows rank []

def sampledData (rows mass suffix : List Bool) (q : SelectorSpec.Result) : Data :=
  {(selectedData rows mass suffix q) with
    row := [], rank := (encodeNat q.rank).drop (RowSemantics.free q.row)
    assignment := RowSemantics.sample q.row q.rank}

theorem unrank_source (row : RowSemantics.Cells) (rank : ℕ) :
    RunsExactly Unrank.computer.step
      (Unrank.config 0 (Dense.CellCodec.encode row) (encodeNat rank) [] [])
      ⟨none, (none, ()), Unrank.tapes [] ((encodeNat rank).drop (RowSemantics.free row)) []
        (RowSemantics.sample row rank)⟩ (2 * row.length + 3) := by
  have hr := Unrank.returns row rank []
  rw [RowSemantics.sample_denote, List.append_nil] at hr
  have he : Unrank.computer.step
      (Unrank.config 2 [] ((encodeNat rank).drop (RowSemantics.free row)) []
        (RowSemantics.sample row rank)) =
      some ⟨none, (none, ()), Unrank.tapes [] ((encodeNat rank).drop (RowSemantics.free row)) []
        (RowSemantics.sample row rank)⟩ := rfl
  convert hr.trans (runsExactly_one he) using 1 <;> omega

theorem unrank_call (rows mass suffix : List Bool) (q : SelectorSpec.Result) :
    RunsExactly computer.step
      (configuration (.unrank 0) initial (selectedData rows mass suffix q))
      (configuration .ownerStart initial (sampledData rows mass suffix q))
      (2 * q.row.length + 3) := by
  apply MachineCall.run unrankStacks Label.unrank .ownerStart unrankState
    Unrank.program program unrank_code initial.2
    (selectedData rows mass suffix q).tapes
    (Unrank.config 0 (Dense.CellCodec.encode q.row) (encodeNat q.rank) [] [])
    ⟨none, (none, ()), Unrank.tapes [] ((encodeNat q.rank).drop (RowSemantics.free q.row)) []
      (RowSemantics.sample q.row q.rank)⟩
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro j h; cases j <;> rfl
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro j h; cases j <;> first
        | rfl
        | exact (h 0 rfl).elim
        | exact (h 1 rfl).elim
        | exact (h 2 rfl).elim
        | exact (h 3 rfl).elim
  · exact unrank_source q.row q.rank

def ownedData (rows mass suffix : List Bool) (q : SelectorSpec.Result) : Data :=
  {(sampledData rows mass suffix q) with
    history := Dense.CellCodec.rows (Owner.remaining q.prior (RowSemantics.sample q.row q.rank))}

def ownedState (answer : Bool) : State := (none, none, none, false, answer)

theorem owner_call (rows mass suffix : List Bool) (q : SelectorSpec.Result)
    (hlen : ∀ row ∈ q.prior, row.length = q.row.length) :
    RunsExactly computer.step
      (configuration (.owner 0) (ownedState true) (sampledData rows mass suffix q))
      (configuration .owned (ownedState (Owner.answer q.prior (RowSemantics.sample q.row q.rank)))
        (ownedData rows mass suffix q))
      (Owner.runTime q.prior (RowSemantics.sample q.row q.rank)) := by
  apply MachineCall.run ownerStacks Label.owner .owned ownerState
    Owner.program program owner_code (none, none)
    (sampledData rows mass suffix q).tapes
    (Owner.config 0 (Dense.CellCodec.rows q.prior) [] (RowSemantics.sample q.row q.rank) [] [])
    (Owner.finished (Owner.answer q.prior (RowSemantics.sample q.row q.rank))
      (Dense.CellCodec.rows (Owner.remaining q.prior (RowSemantics.sample q.row q.rank)))
      (RowSemantics.sample q.row q.rank))
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro j h; cases j <;> rfl
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro j h; cases j <;> first
        | rfl
        | exact (h 0 rfl).elim
        | exact (h 1 rfl).elim
        | exact (h 2 rfl).elim
        | exact (h 3 rfl).elim
        | exact (h 4 rfl).elim
  · exact Owner.run_exact q.prior (RowSemantics.sample q.row q.rank)
      (by simpa only [RowSemantics.sample_length] using hlen)

end Counting.Algorithm.KarpLubyRequest.Sampling.Trial
