import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Program
import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Bank

/-! # Full physical banks for the group caller -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby

def word (rows mass samples history randomTape : List Bool) : List Bool :=
  Encoding.frame rows ++ Encoding.frame mass ++ Encoding.frame samples ++
    Encoding.frame history ++ randomTape

/-- All unlisted inner source stacks are empty. The six outer field words are
physical Boolean stacks, not members of the finite register. -/
def bank (count randomWord : List Bool) (fields : Fin 6 → List Bool) : Stack → List Bool :=
  Sum.elim (Iteration.ready SampleBody.machine count randomWord) fields

def fields (rowWord massWord sampleWord history result work : List Bool) : Fin 6 → List Bool :=
  ![rowWord, massWord, sampleWord, history, result, work]

def emptyFields : Fin 6 → List Bool := fun _ => []

def ready (rowWord massWord sampleWord history randomWord : List Bool) : Stack → List Bool :=
  bank [] randomWord (fields rowWord massWord sampleWord history [] [])

def config (label : Label) (tape : Stack → List Bool) : computer.Cfg :=
  ⟨some label, initial, tape⟩

def halted (output : List Bool) : computer.Cfg :=
  ⟨none, initial, bank [] output emptyFields⟩

theorem bank_random (count randomWord : List Bool) (fields : Fin 6 → List Bool) :
    bank count randomWord fields random = randomWord :=
  wordTape_at SampleBody.random randomWord

theorem bank_counter (count randomWord : List Bool) (fields : Fin 6 → List Bool) :
    bank count randomWord fields counter = count := rfl

theorem bank_field (count randomWord : List Bool) (fields : Fin 6 → List Bool) (k : Fin 6) :
    bank count randomWord fields (.inr k) = fields k := rfl

theorem update_field (count randomWord : List Bool) (fields : Fin 6 → List Bool)
    (k : Fin 6) (replacement : List Bool) :
    Function.update (bank count randomWord fields) (.inr k) replacement =
      bank count randomWord (Function.update fields k replacement) := by
  funext j
  cases j <;> simp [bank, Function.update_apply]

theorem update_random (count randomWord : List Bool) (fields : Fin 6 → List Bool)
    (replacement : List Bool) :
    Function.update (bank count randomWord fields) random replacement = bank count replacement fields := by
  funext j
  cases j with
  | inr j => rfl
  | inl j =>
    cases j with
    | inl j => fin_cases j <;> rfl
    | inr j =>
      by_cases hj : j = SampleBody.random
      · subst j; rfl
      · have ho : (Sum.inl (Sum.inr j) : Stack) ≠ random := by
          intro h; exact hj (Sum.inr.inj (Sum.inl.inj h))
        rw [Function.update_of_ne ho]
        change wordTape SampleBody.random randomWord j = wordTape SampleBody.random replacement j
        exact (wordTape_other SampleBody.random j randomWord hj).trans
          (wordTape_other SampleBody.random j replacement hj).symm

theorem update_counter (count randomWord : List Bool) (fields : Fin 6 → List Bool)
    (replacement : List Bool) :
    Function.update (bank count randomWord fields) counter replacement = bank replacement randomWord fields := by
  funext j
  cases j with
  | inr j => rfl
  | inl j =>
    cases j with
    | inl j => fin_cases j <;> rfl
    | inr j => rfl

theorem bank_empty (word : List Bool) : bank [] word emptyFields = wordTape random word := by
  funext j
  cases j with
  | inr j => rfl
  | inl j =>
    cases j with
    | inl j => fin_cases j <;> rfl
    | inr j =>
      by_cases hj : j = SampleBody.random
      · subst j; rfl
      · have ho : (Sum.inl (Sum.inr j) : Stack) ≠ random := by
          intro h; exact hj (Sum.inr.inj (Sum.inl.inj h))
        rw [wordTape_other _ _ _ ho]
        exact wordTape_other SampleBody.random j word hj

theorem init_word (input : List Bool) :
    initList computer input = config (.scan 0) (bank [] input emptyFields) := by
  rw [machine.init_eq, bank_empty]
  rfl

theorem halt_word (output : List Bool) : haltList computer output = halted output := by
  rw [machine.halt_eq, halted, bank_empty]
  rfl

theorem finish_step (output : List Bool) :
    computer.step (config .done (bank [] output emptyFields)) = some (halted output) := rfl

end Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
