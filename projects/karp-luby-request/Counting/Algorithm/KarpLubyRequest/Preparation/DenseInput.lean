import Counting.Algorithm.KarpLubyRequest.Preparation.Calls
import Counting.Algorithm.KarpLubyRequest.Preparation.Transfers
import Counting.Algorithm.KarpLubyRequest.Preparation.BankUpdates

/-! The retained parser fields are copied by the actual caller loops into the
finite dense normalizer bank. Both copies are charged and original words remain. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

def variableWord (source : RequestParser.Stack → List Bool) : List Bool :=
  source (RequestParser.headerMap ProblemHeader.destination)
def formulaWord (source : RequestParser.Stack → List Bool) : List Bool :=
  source (RequestParser.headerMap ProblemHeader.source)
def randomWord (source : RequestParser.Stack → List Bool) : List Bool :=
  source (RequestParser.headerMap (.inl 0))

def validatedData (source : RequestParser.Stack → List Bool) : Data :=
  parameterData (ParameterValidation.prepared source 4)
def denseData (source : RequestParser.Stack → List Bool) : Data :=
  {validatedData source with formula :=
    (Dense.Formula.bank (variableWord source) (formulaWord source) [] [] [] [] [] [])}

theorem variableWord_stored (source : RequestParser.Stack → List Bool) :
    (validatedData source).tapes variableSource = variableWord source := rfl
theorem formulaWord_stored (source : RequestParser.Stack → List Bool) :
    (validatedData source).tapes formulaSource = formulaWord source := rfl

theorem dense_input_copy (source : RequestParser.Stack → List Bool) (memory : Memory) :
    RunsExactly computer.step (cfg (.copyMove .variables) memory (validatedData source).tapes)
      (cfg (.formula .copy) memory (denseData source).tapes)
      (2 * ((variableWord source).length + (formulaWord source).length) + 4) := by
  let first : Data := {validatedData source with
    formula := Function.update (fun _ => []) 0 (variableWord source)}
  have h0 := copy_run .variables memory (validatedData source).tapes rfl rfl
  change RunsExactly computer.step _
    (cfg (.copyMove .formula) memory
      (Function.update (validatedData source).tapes (formulaStacks 0) (variableWord source))) _ at h0
  rw [update_formula] at h0
  have h1 := copy_run .formula memory first.tapes rfl rfl
  change RunsExactly computer.step _
    (cfg (.formula .copy) memory
      (Function.update first.tapes (formulaStacks 8) (formulaWord source))) _ at h1
  rw [update_formula] at h1
  have he : ({first with formula := Function.update first.formula 8 (formulaWord source)} : Data)
      = denseData source := by
    have hf : Function.update first.formula 8 (formulaWord source) =
        Dense.Formula.bank (variableWord source) (formulaWord source) [] [] [] [] [] [] := by
      funext k; fin_cases k <;> rfl
    rw [hf]
    rfl
  rw [he] at h1
  have e0 : (validatedData source).tapes (copySource .variables) = variableWord source := rfl
  have e1 : first.tapes (copySource .formula) = formulaWord source := rfl
  rw [e0] at h0
  rw [e1] at h1
  convert h0.trans h1 using 1 <;> first | rfl | omega

/-- The validator's accepted flag dispatches by one real transition; it does
not install any field or alter the retained source bank. -/
theorem validated_true (memory : Memory) (bank : Stack → List Bool)
    (hv : memory.parameter.1 = true) :
    RunsExactly computer.step (cfg .validated memory bank)
      (cfg (.copyMove .variables) memory bank) 1 := by
  apply runsExactly_one
  change some (TM2.stepAux (program .validated) (none, memory) bank) = _
  dsimp only [program, TM2.stepAux]
  rw [hv]
  rfl

theorem validated_false (memory : Memory) (bank : Stack → List Bool)
    (hv : memory.parameter.1 = false) :
    RunsExactly computer.step (cfg .validated memory bank) (cfg .zero memory bank) 1 := by
  apply runsExactly_one
  change some (TM2.stepAux (program .validated) (none, memory) bank) = _
  dsimp only [program, TM2.stepAux]
  rw [hv]
  rfl

end
end Counting.Algorithm.KarpLubyRequest.Preparation
