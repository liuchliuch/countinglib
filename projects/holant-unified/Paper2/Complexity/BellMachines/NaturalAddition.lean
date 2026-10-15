import Paper2.Complexity.BellMachines.BinaryArithmetic.EncodedAddition
import Paper2.Complexity.BellMachines.FixedFieldMachines.LeftMap
import Paper2.Complexity.BellMachines.FixedFieldMachines.Reverse

/-! Literal forward canonical natural-word addition. Reversal bridges the
existing arithmetic parser, and both reversals are actual finite programs. -/
namespace Paper2.Complexity.BellMachines
open Turing Computability BinaryCompose FixedFieldMachines

abbrev naturalAdditionMachine : BinaryCompose.Machine where
  K := BinaryArithmetic.EncodedAddition.computer.K
  input := BinaryArithmetic.EncodedAddition.computer.k₀
  output := BinaryArithmetic.EncodedAddition.computer.k₁
  Label := BinaryArithmetic.EncodedAddition.computer.Λ
  main := BinaryArithmetic.EncodedAddition.computer.main
  State := BinaryArithmetic.EncodedAddition.computer.σ
  initial := BinaryArithmetic.EncodedAddition.computer.initialState
  program := BinaryArithmetic.EncodedAddition.computer.m

noncomputable def naturalAdditionInternal :
    Computes BinaryArithmetic.EncodedAddition.inputEncoding encodingNatBool
      (fun p => p.1 + p.2) where
  machine := naturalAdditionMachine
  time := BinaryArithmetic.EncodedAddition.additionPolyTime.time
  outputs p := by
    have h := BinaryArithmetic.EncodedAddition.additionPolyTime.outputsFun p
    change TM2OutputsInTime naturalAdditionMachine.computer
      (List.map id (BinaryArithmetic.EncodedAddition.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (p.1 + p.2)))) _ at h
    simpa only [List.map_id] using h

noncomputable def naturalAddition :
    Computes (pairEncoding encodingNatBool encodingNatBool) encodingNatBool
      (fun p => p.1 + p.2) := by
  let prepare := pairComputes
    ((Wiring.firstComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
    ((Wiring.secondComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
  let recoded : Computes (pairEncoding encodingNatBool encodingNatBool)
      BinaryArithmetic.EncodedAddition.inputEncoding id :=
    recode prepare id (fun _ => rfl) (fun _ => rfl)
  exact recoded.andThen naturalAdditionInternal

end Paper2.Complexity.BellMachines
