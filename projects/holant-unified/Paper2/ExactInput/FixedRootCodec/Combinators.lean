import Paper2.TractableAlgorithms.Paper1Machine
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Combinators

/-! Fixed finite conditional circuits, reusing the actual proved Boolean
selector program. Tests and both candidates are computed by finite programs;
selection and all candidate work are included in the polynomial transition
bound. No host-language conditional becomes a machine instruction. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Complexity Paper2.Complexity.BinaryCompose
open FixedFieldMachines
noncomputable section

def sourceMachine (m : Machine) : Holant.Complexity.BinaryCompose.Machine where
  K := m.K
  decidableK := m.decidableK
  finiteK := m.finiteK
  input := m.input
  output := m.output
  Label := m.Label
  finiteLabel := m.finiteLabel
  main := m.main
  State := m.State
  finiteState := m.finiteState
  initial := m.initial
  program := m.program

def sourceComputes {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (m : Computes ea eb f) :
    Holant.Complexity.BinaryCompose.Computes ea eb f where
  machine := sourceMachine m.machine
  time := m.time
  outputs := m.outputs

def ifComputes {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {p : A → Bool} {f g : A → B} (test : Computes ea encodingBoolBool p)
    (yes : Computes ea eb f) (no : Computes ea eb g) :
    Computes ea eb (fun a => if p a then f a else g a) :=
  TractableAlgorithms.Paper1Machine.computes
    (Holant.Complexity.UniversalPairReduction.SmoothingCompiler.ifComputes
      (sourceComputes test) (sourceComputes yes) (sourceComputes no))

def equalComputes {A : Type} [DecidableEq A] (e : Encoding A Bool) :
    Computes (pairEncoding e e) encodingBoolBool (fun p => decide (p.1 = p.2)) :=
  recode
    (TractableAlgorithms.Paper1Machine.computes
      (Holant.Complexity.UniversalPairReduction.SmoothingCompiler.equalComputes e))
    id
    (fun p => congrArg (fun w => w ++ e.encode p.2)
      (TractableAlgorithms.Paper1Machine.frame_eq (e.encode p.1)))
    (fun _ => rfl)

def zeroComputes {A : Type} [DecidableEq A] [Zero A] (e : Encoding A Bool) :
    Computes e encodingBoolBool (fun x => decide (x = 0)) :=
  congrComputes
    ((pairComputes (identityComputes e) (constantComputes e e 0)).andThen (equalComputes e))
    (fun _ => rfl)

end
end Paper2.ExactInput.FixedRootCodec
