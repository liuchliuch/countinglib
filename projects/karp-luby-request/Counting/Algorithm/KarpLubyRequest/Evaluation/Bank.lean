import Counting.Algorithm.KarpLubyRequest.Evaluation.Program
import Counting.Algorithm.KarpLubyRequest.BankProtocol

/-! Complete physical banks for the post-validation evaluator. -/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby

structure Data where
  outer : OuterStack → List Bool := fun _ => []
  fields : Fin 6 → List Bool := fun _ => []
  median : Median.Program.Stack → List Bool := fun _ => []
  output : Output.Program.Stack → List Bool := fun _ => []

def Data.tapes (d : Data) : Stack → List Bool :=
  Sum.elim d.outer (Sum.elim d.fields (Sum.elim d.median d.output))

def configuration (label : Label) (state : State) (d : Data) : computer.Cfg :=
  ⟨some label, state, d.tapes⟩

def fieldWords (r m s g a work : List Bool) : Fin 6 → List Bool :=
  fun k => match k.val with | 0 => r | 1 => m | 2 => s | 3 => g | 4 => a | _ => work

def inputData (word : List Bool) : Data :=
  { outer := wordTape (Iteration.bodyStack Sampling.GroupBody.machine Sampling.GroupBody.random) word }

def finalData (word : List Bool) : Data :=
  { output := wordTape Output.Program.computer.k₁ word }

def finalConfiguration (word : List Bool) : computer.Cfg :=
  ⟨none, initial, (finalData word).tapes⟩

def payload (r m s g tape : List Bool) : List Bool :=
  true :: (Encoding.frame r ++ (Encoding.frame m ++
    (Encoding.frame s ++ (Encoding.frame g ++ tape))))

@[simp] theorem tapes_outer (d : Data) (k : OuterStack) : d.tapes (outerStacks k) = d.outer k := rfl
@[simp] theorem tapes_field (d : Data) (i : Fin 6) : d.tapes (extra i) = d.fields i := rfl
@[simp] theorem tapes_median (d : Data) (k : Median.Program.Stack) :
    d.tapes (medianStacks k) = d.median k := rfl
@[simp] theorem tapes_output (d : Data) (k : Output.Program.Stack) :
    d.tapes (outputStacks k) = d.output k := rfl

theorem update_outer (d : Data) (k : OuterStack) (word : List Bool) :
    Function.update d.tapes (outerStacks k) word =
      ({d with outer := Function.update d.outer k word} : Data).tapes := by
  funext j
  cases j <;> simp [Data.tapes, outerStacks, Function.update_apply]

theorem update_field (d : Data) (i : Fin 6) (word : List Bool) :
    Function.update d.tapes (extra i) word =
      ({d with fields := Function.update d.fields i word} : Data).tapes := by
  funext j
  rcases j with j | (j | (j | j))
  · rfl
  · by_cases hj : j = i
    · subst j
      change Function.update d.tapes (extra i) word (extra i) = Function.update d.fields i word i
      rw [Function.update_self, Function.update_self]
    · have ho : extra j ≠ extra i := fun h => hj (Sum.inl.inj (Sum.inr.inj h))
      change Function.update d.tapes (extra i) word (extra j) = _
      rw [Function.update_of_ne ho]
      exact (Function.update_of_ne hj word d.fields).symm
  · rfl
  · rfl

theorem update_median (d : Data) (k : Median.Program.Stack) (word : List Bool) :
    Function.update d.tapes (medianStacks k) word =
      ({d with median := Function.update d.median k word} : Data).tapes := by
  funext j
  rcases j with j | (j | (j | j))
  · rfl
  · rfl
  · by_cases hj : j = k
    · subst j
      change Function.update d.tapes (medianStacks k) word (medianStacks k) = Function.update d.median k word k
      rw [Function.update_self, Function.update_self]
    · have ho : medianStacks j ≠ medianStacks k := fun h => hj (medianStacks.injective h)
      change Function.update d.tapes (medianStacks k) word (medianStacks j) = _
      rw [Function.update_of_ne ho]
      exact (Function.update_of_ne hj word d.median).symm
  · rfl

theorem update_output (d : Data) (k : Output.Program.Stack) (word : List Bool) :
    Function.update d.tapes (outputStacks k) word =
      ({d with output := Function.update d.output k word} : Data).tapes := by
  funext j
  rcases j with j | (j | (j | j))
  · rfl
  · rfl
  · rfl
  · by_cases hj : j = k
    · subst j
      change Function.update d.tapes (outputStacks k) word (outputStacks k) = Function.update d.output k word k
      rw [Function.update_self, Function.update_self]
    · have ho : outputStacks j ≠ outputStacks k := fun h => hj (outputStacks.injective h)
      change Function.update d.tapes (outputStacks k) word (outputStacks j) = _
      rw [Function.update_of_ne ho]
      exact (Function.update_of_ne hj word d.output).symm

theorem input_eq (word : List Bool) : initList computer word =
    configuration .dispatch initial (inputData word) := by
  rw [Machine.init_eq]
  congr 1
  funext j
  cases j with
  | inr j => rcases j with j | (j | j) <;> rfl
  | inl j =>
    by_cases hj : j = Iteration.bodyStack Sampling.GroupBody.machine Sampling.GroupBody.random
    · subst j; rfl
    · change wordTape random word (outerStacks j) = _
      exact (wordTape_other random (outerStacks j) word
        (fun h => hj (outerStacks.injective h))).trans
        (wordTape_other _ _ word hj).symm

theorem halt_eq (word : List Bool) : haltList computer word = finalConfiguration word := by
  rw [Machine.halt_eq]
  congr 1
  funext j
  rcases j with j | (j | (j | j))
  · rfl
  · rfl
  · rfl
  · by_cases hj : j = Output.Program.computer.k₁
    · subst j; rfl
    · change wordTape result word (outputStacks j) = _
      exact (wordTape_other result (outputStacks j) word
        (fun h => hj (outputStacks.injective h))).trans
        (wordTape_other _ _ word hj).symm

end Counting.Algorithm.KarpLubyRequest.Evaluation
