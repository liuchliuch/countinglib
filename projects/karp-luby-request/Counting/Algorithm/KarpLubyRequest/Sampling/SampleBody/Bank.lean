import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Program

/-! # Physical banks and the state-word layout of a sample body -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby

/-- This is a storage specification; no whole-word operation occurs in control. -/
def word (rows mass acc randomTape : List Bool) : List Bool :=
  Encoding.frame rows ++ Encoding.frame mass ++ Encoding.frame acc ++ randomTape

def tapes (d : Trial.Data) (acc work output : List Bool) : Stack → List Bool
  | .inl k => d.tapes k
  | .inr k => match k.val with
    | 0 => acc
    | 1 => work
    | _ => output

def ready (rows mass randomTape acc result : List Bool) : Stack → List Bool :=
  tapes ({Trial.inputData rows mass randomTape with output := result}) acc [] []

def summed (rows mass randomTape acc : List Bool) : Stack → List Bool :=
  tapes (Trial.inputData rows mass randomTape) [] [] acc

def config (label : Label) (tape : Stack → List Bool) : computer.Cfg :=
  ⟨some label, Trial.initial, tape⟩

def halted (output : List Bool) : computer.Cfg :=
  ⟨none, Trial.initial, ready [] [] output [] []⟩

theorem ready_wordTape (output : List Bool) :
    ready [] [] output [] [] = wordTape random output := by
  funext k
  cases k with
  | inl k => cases k <;> simp [ready, tapes, Trial.inputData, Trial.Data.tapes, wordTape, random]
  | inr k => fin_cases k <;> simp [ready, tapes, wordTape, random]

theorem init_word (input : List Bool) :
    initList computer input = config (.scan 0) (ready [] [] input [] []) := by
  rw [machine.init_eq]
  rw [ready_wordTape]
  rfl

theorem halt_word (output : List Bool) : haltList computer output = halted output := by
  rw [machine.halt_eq]
  rw [halted, ready_wordTape]
  rfl

theorem finish_step (output : List Bool) :
    computer.step (config .done (ready [] [] output [] [])) = some (halted output) := by rfl

end Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
