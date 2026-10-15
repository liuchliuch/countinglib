import Paper2.Complexity.BellMachines.BinaryArithmetic.EncodedComparison
import Paper2.Complexity.BellMachines.FixedFieldMachines.LeftMap
import Paper2.Complexity.BellMachines.FixedFieldMachines.Reverse

/-! Literal forward canonical natural-word comparison. Reversal bridges the
existing arithmetic parser, and both reversals are actual finite programs. -/
namespace Paper2.Complexity.BellMachines
open Turing Computability BinaryCompose FixedFieldMachines

abbrev naturalComparisonMachine : BinaryCompose.Machine where
  K := BinaryArithmetic.EncodedComparison.computer.K
  input := BinaryArithmetic.EncodedComparison.computer.k₀
  output := BinaryArithmetic.EncodedComparison.computer.k₁
  Label := BinaryArithmetic.EncodedComparison.computer.Λ
  main := BinaryArithmetic.EncodedComparison.computer.main
  State := BinaryArithmetic.EncodedComparison.computer.σ
  initial := BinaryArithmetic.EncodedComparison.computer.initialState
  program := BinaryArithmetic.EncodedComparison.computer.m

noncomputable def naturalComparisonInternal :
    Computes BinaryArithmetic.EncodedComparison.inputEncoding encodingBoolBool
      (fun p => decide (p.1 < p.2)) where
  machine := naturalComparisonMachine
  time := BinaryArithmetic.EncodedComparison.comparisonPolyTime.time
  outputs p := by
    have h := BinaryArithmetic.EncodedComparison.comparisonPolyTime.outputsFun p
    change TM2OutputsInTime naturalComparisonMachine.computer
      (List.map id (BinaryArithmetic.EncodedComparison.inputEncoding.encode p))
      (some (List.map id (encodingBoolBool.encode (decide (p.1 < p.2))))) _ at h
    simpa only [List.map_id] using h

noncomputable def naturalComparison :
    Computes (pairEncoding encodingNatBool encodingNatBool) encodingBoolBool
      (fun p => decide (p.1 < p.2)) := by
  let prepare := pairComputes
    ((Wiring.firstComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
    ((Wiring.secondComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
  let recoded : Computes (pairEncoding encodingNatBool encodingNatBool)
      BinaryArithmetic.EncodedComparison.inputEncoding id :=
    recode prepare id (fun _ => rfl) (fun _ => rfl)
  exact recoded.andThen naturalComparisonInternal

end Paper2.Complexity.BellMachines
