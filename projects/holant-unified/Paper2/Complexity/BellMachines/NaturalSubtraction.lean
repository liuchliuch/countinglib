import Paper2.Complexity.BellMachines.BinaryArithmetic.EncodedSubtraction
import Paper2.Complexity.BellMachines.FixedFieldMachines.LeftMap
import Paper2.Complexity.BellMachines.FixedFieldMachines.Reverse

/-! Literal forward canonical natural-word subtraction. Reversal bridges the
existing arithmetic parser, and both reversals are actual finite programs. -/
namespace Paper2.Complexity.BellMachines
open Turing Computability BinaryCompose FixedFieldMachines

abbrev naturalSubtractionMachine : BinaryCompose.Machine where
  K := BinaryArithmetic.EncodedSubtraction.computer.K
  input := BinaryArithmetic.EncodedSubtraction.computer.k₀
  output := BinaryArithmetic.EncodedSubtraction.computer.k₁
  Label := BinaryArithmetic.EncodedSubtraction.computer.Λ
  main := BinaryArithmetic.EncodedSubtraction.computer.main
  State := BinaryArithmetic.EncodedSubtraction.computer.σ
  initial := BinaryArithmetic.EncodedSubtraction.computer.initialState
  program := BinaryArithmetic.EncodedSubtraction.computer.m

noncomputable def naturalSubtractionInternal :
    Computes BinaryArithmetic.EncodedSubtraction.inputEncoding encodingNatBool
      (fun p => p.1 - p.2) where
  machine := naturalSubtractionMachine
  time := BinaryArithmetic.EncodedSubtraction.subtractionPolyTime.time
  outputs p := by
    have h := BinaryArithmetic.EncodedSubtraction.subtractionPolyTime.outputsFun p
    change TM2OutputsInTime naturalSubtractionMachine.computer
      (List.map id (BinaryArithmetic.EncodedSubtraction.inputEncoding.encode p))
      (some (List.map id (encodingNatBool.encode (p.1 - p.2)))) _ at h
    simpa only [List.map_id] using h

noncomputable def naturalSubtraction :
    Computes (pairEncoding encodingNatBool encodingNatBool) encodingNatBool
      (fun p => p.1 - p.2) := by
  let prepare := pairComputes
    ((Wiring.firstComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
    ((Wiring.secondComputes encodingNatBool encodingNatBool).andThen (reverseComputes encodingNatBool))
  let recoded : Computes (pairEncoding encodingNatBool encodingNatBool)
      BinaryArithmetic.EncodedSubtraction.inputEncoding id :=
    recode prepare id (fun _ => rfl) (fun _ => rfl)
  exact recoded.andThen naturalSubtractionInternal

end Paper2.Complexity.BellMachines
