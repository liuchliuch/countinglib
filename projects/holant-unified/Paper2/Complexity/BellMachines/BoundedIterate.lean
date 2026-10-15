import Paper2.Complexity.BellMachines.GraphPreprocessing.Call
import Paper2.Complexity.BellMachines.FixedFieldMachines.LeftMap
import Paper2.Complexity.BellMachines.MoveWord
import Paper2.Complexity.BellMachines.GraphPreprocessing.UnaryBinary

/-! A finite returning controller for unary-bounded iteration. Every round
executes an actual finite subprogram and physically transfers its clean output
back into its input. There is no host-level iteration instruction. -/
namespace Paper2.Complexity.BellMachines.BoundedIterate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines GraphPreprocessing
open Turing.TM2.Stmt
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

abbrev Stack := m.K ⊕ Fin 3
abbrev Label := m.Label ⊕ Fin 8
abbrev Statement := TM2.Stmt (fun _ : Stack m => Bool) (Label m) (Option Bool × m.State)
def inputKey : Stack m := .inr 0
def countKey : Stack m := .inr 1
def tempKey : Stack m := .inr 2

def outside (i : Fin 8) : Statement m := match i.val with
  | 0 => Frame.scanStmt (inputKey m) (tempKey m) (.inr 0) (.inr 1) (.inr 7)
  | 1 => copyMoveStmt (tempKey m) (countKey m) (.inr 1) (.inr 2)
  | 2 => copyMoveStmt (inputKey m) (tempKey m) (.inr 2) (.inr 3)
  | 3 => copyMoveStmt (tempKey m) (.inl m.input) (.inr 3) (.inr 4)
  | 4 => pop (countKey m) (fun st bit => (bit,st.2))
    (branch (fun st => st.1.isSome)
      (load (fun st => (none,st.2)) (goto (fun _ => .inl m.main)))
      (load (fun st => (none,st.2)) (goto (fun _ => .inr 7))))
  | 5 => copyMoveStmt (.inl m.output) (tempKey m) (.inr 5) (.inr 6)
  | 6 => copyMoveStmt (tempKey m) (.inl m.input) (.inr 6) (.inr 4)
  | _ => .halt

def program : Label m → Statement m
  | .inl l => Call.statement (LeftMap.states m) Sum.inl (some (.inr (5 : Fin 8))) (m.program l)
  | .inr i => outside m i

abbrev machine : Machine where
  K := Stack m
  input := inputKey m
  output := .inl m.input
  Label := Label m
  main := .inr 0
  State := Option Bool × m.State
  initial := (none,m.initial)
  program := program m

def extras (input count temp : List Bool) : Fin 3 → List Bool := ![input,count,temp]
def tapes (source : m.K → List Bool) (input count temp : List Bool) : Stack m → List Bool :=
  Sum.elim source (extras input count temp)
def config (label : Label m) (source : m.K → List Bool) (input count temp : List Bool) :=
  cfg label m.initial (tapes m source input count temp)
def ready (label : Label m) (word count : List Bool) :=
  config m label (wordTape m.input word) [] count []

@[simp] theorem update_input (s : m.K → List Bool) (i c t w : List Bool) :
    Function.update (tapes m s i c t) (inputKey m) w = tapes m s w c t := by
  funext k; rcases k with k | k
  · simp [tapes,inputKey,Function.update]
  · fin_cases k <;> simp [tapes,extras,inputKey,Function.update]
@[simp] theorem update_count (s : m.K → List Bool) (i c t w : List Bool) :
    Function.update (tapes m s i c t) (countKey m) w = tapes m s i w t := by
  funext k; rcases k with k | k
  · simp [tapes,countKey,Function.update]
  · fin_cases k <;> simp [tapes,extras,countKey,Function.update]
@[simp] theorem update_temp (s : m.K → List Bool) (i c t w : List Bool) :
    Function.update (tapes m s i c t) (tempKey m) w = tapes m s i c w := by
  funext k; rcases k with k | k
  · simp [tapes,tempKey,Function.update]
  · fin_cases k <;> simp [tapes,extras,tempKey,Function.update]
@[simp] theorem update_source (s : m.K → List Bool) (i c t w : List Bool) (k : m.K) :
    Function.update (tapes m s i c t) (.inl k) w = tapes m (Function.update s k w) i c t := by
  funext j; rcases j with j | j
  · simp [tapes,Function.update]
  · simp [tapes,Function.update]
@[simp] theorem update_word (k : m.K) (a b : List Bool) :
    Function.update (wordTape k a) k b = wordTape k b := by simp [wordTape]
@[simp] theorem empty_word (k : m.K) : wordTape k [] = (fun _ => []) := by
  funext j; simp [wordTape]

end Paper2.Complexity.BellMachines.BoundedIterate
