import Counting.Algorithm.KarpLubyRequest.RequestParser
import Counting.Algorithm.KarpLubyRequest.StateAdapter
import Counting.Algorithm.KarpLubyRequest.ParameterWords
import Counting.Algorithm.KarpLubyRequest.ParameterSemantics
import Holant.Complexity.BinaryArithmetic.Comparison

/-!
# A single finite parser and accuracy-check program

The raw request parser is followed by sign/zero checks, four retained-word
canonicalizations, and two calls to the canonical H1 unsigned comparator.
Accuracy and confidence are binary rational fields, not unary loop counters.
Every original header field, including the fair-bit tape, is retained. Finite
control never evaluates a rational or decodes a natural number.
-/
namespace Counting.Algorithm.KarpLubyRequest.ParameterProgram
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

abbrev Stack := RequestParser.Stack ⊕ Fin 10
abbrev Label := RequestParser.Label ⊕ ((Fin 4 × Fin 5) ⊕ (Bool ⊕ Fin 15))
abbrev Memory := Bool × BinaryArithmetic.Comparison.State
abbrev State := Option Bool × Memory
instance stackDecidable : DecidableEq Stack :=
  @instDecidableEqSum RequestParser.Stack (Fin 10) RequestParser.computer.kDecidableEq inferInstance

instance stateFinite : Fintype State := by
  letI : Fintype (Option Bool × Bool) := RequestParser.computer.σFin
  letI : Fintype BinaryArithmetic.Comparison.State := BinaryArithmetic.Comparison.computer.σFin
  exact Fintype.ofEquiv ((Option Bool × Bool) × BinaryArithmetic.Comparison.State)
    (Equiv.prodAssoc _ _ _)

instance stackFinite : Fintype Stack := by
  letI : Fintype RequestParser.Stack := RequestParser.computer.kFin
  exact inferInstanceAs (Fintype (RequestParser.Stack ⊕ Fin 10))

instance labelFinite : Fintype Label := by
  letI : Fintype RequestParser.Label := RequestParser.computer.ΛFin
  exact inferInstanceAs (Fintype (RequestParser.Label ⊕ ((Fin 4 × Fin 5) ⊕ (Bool ⊕ Fin 15))))

abbrev Config := Cfg Stack Label Memory

def parserMap : RequestParser.Stack ↪ Stack := ⟨Sum.inl, Sum.inl_injective⟩
@[simp] theorem parserMap_apply (k : RequestParser.Stack) : parserMap k = .inl k := rfl
def extra (k : Fin 10) : Stack := .inr k

def parserLabel (l : RequestParser.Label) : Label := .inl l
def wordLabel (i : Fin 4) (l : Fin 5) : Label := .inr (.inl (i, l))
def compareLabel (strict : Bool) (_ : Unit) : Label := .inr (.inr (.inl strict))
def control (l : Fin 15) : Label := .inr (.inr (.inr l))

def parserState : (RequestParser.computer.σ × BinaryArithmetic.Comparison.State) ≃ State :=
  Equiv.prodAssoc _ _ _
def comparisonState : (BinaryArithmetic.Comparison.State × (Option Bool × Bool)) ≃ State :=
  (Equiv.prodComm _ _).trans (Equiv.prodAssoc _ _ _)

def field (i : Fin 4) : Stack :=
  parserMap (RequestParser.headerMap (.inl (![5, 2, 7, 3] i)))
def sign (delta : Bool) : Stack :=
  parserMap (RequestParser.headerMap (.inl (if delta then 8 else 6)))
def canonical (i : Fin 4) : Stack := extra ⟨i.val + 1, by omega⟩

def wordMap (i : Fin 4) : ParameterWords.Stacks Stack :=
  ⟨fun k => (![field i, extra 0, canonical i, extra 8] : Fin 4 → Stack) k,
    by
      intro a b h
      fin_cases i <;> fin_cases a <;> fin_cases b <;> simp_all [field, canonical, extra]⟩
@[simp] theorem wordMap_zero (i : Fin 4) : wordMap i 0 = field i := rfl
@[simp] theorem wordMap_one (i : Fin 4) : wordMap i 1 = extra 0 := rfl
@[simp] theorem wordMap_two (i : Fin 4) : wordMap i 2 = canonical i := rfl
@[simp] theorem wordMap_three (i : Fin 4) : wordMap i 3 = extra 8 := rfl

def afterWord (i : Fin 4) : Label :=
  if h : i.val < 3 then wordLabel ⟨i.val + 1, by omega⟩ 0 else control 3

def wordLabels (i : Fin 4) : ParameterWords.Labels Label :=
  ⟨wordLabel i 0, wordLabel i 1, wordLabel i 2, wordLabel i 3, wordLabel i 4, afterWord i⟩

def wordCode (i : Fin 4) (l : Fin 5) : Stmt Stack Label Memory :=
  if l = 0 then copyMoveStmt (field i) (extra 8) (wordLabel i 0) (wordLabel i 1)
  else if l = 1 then copyRestoreStmt (field i) (extra 0) (extra 8) (wordLabel i 1) (wordLabel i 2)
  else if l = 2 then copyMoveStmt (extra 0) (extra 8) (wordLabel i 2) (wordLabel i 3)
  else if l = 3 then NaturalWords.highestStmt (extra 8) (canonical i) (wordLabel i 4)
  else copyMoveStmt (extra 8) (canonical i) (wordLabel i 4) (afterWord i)

def comparisonMap : BinaryArithmetic.Comparison.Stack ↪ Stack :=
  ⟨fun k => match k with
      | .left => extra 5 | .right => extra 6 | .work => extra 9 | .out => extra 7,
    by intro a b h; cases a <;> cases b <;> simp_all [extra]⟩

def returnCompare (strict : Bool) : Label := if strict then control 12 else control 7

/-- Two physical peeks decide sign and nonzero magnitude, without consuming
any retained field or invoking a semantic decoder in a transition. -/
def positiveStmt (delta : Bool) (next : Label) : Stmt Stack Label Memory :=
  .peek (sign delta) (fun v b => (b, v.2))
    (.branch (fun v => v.1 == some false)
      (.peek (field (if delta then 2 else 0)) (fun v b => (b, v.2))
        (.branch (fun v => v.1.isSome)
          (.load (fun v => (none, v.2)) (.goto (fun _ => next)))
          (.goto (fun _ => control 14))))
      (.goto (fun _ => control 14)))

def outside (l : Fin 15) : Stmt Stack Label Memory :=
  if l = 0 then .branch (fun v => v.2.1) (.goto (fun _ => control 1)) (.goto (fun _ => control 14))
  else if l = 1 then positiveStmt false (control 2)
  else if l = 2 then positiveStmt true (wordLabel 0 0)
  else if l = 3 then copyMoveStmt (canonical 1) (extra 8) (control 3) (control 4)
  else if l = 4 then copyRestoreStmt (canonical 1) (extra 5) (extra 8) (control 4) (control 5)
  else if l = 5 then copyMoveStmt (canonical 0) (extra 8) (control 5) (control 6)
  else if l = 6 then copyRestoreStmt (canonical 0) (extra 6) (extra 8) (control 6) (compareLabel false ())
  else if l = 7 then .pop (extra 7) (fun v b => (b, v.2))
    (.branch (fun v => v.1.getD true) (.goto (fun _ => control 14))
      (.load (fun v => (none, v.2)) (.goto (fun _ => control 8))))
  else if l = 8 then copyMoveStmt (canonical 2) (extra 8) (control 8) (control 9)
  else if l = 9 then copyRestoreStmt (canonical 2) (extra 5) (extra 8) (control 9) (control 10)
  else if l = 10 then copyMoveStmt (canonical 3) (extra 8) (control 10) (control 11)
  else if l = 11 then copyRestoreStmt (canonical 3) (extra 6) (extra 8) (control 11) (compareLabel true ())
  else if l = 12 then .pop (extra 7) (fun v b => (b, v.2))
    (.branch (fun v => v.1.getD false)
      (.load (fun v => (none, v.2)) (.goto (fun _ => control 13))) (.goto (fun _ => control 14)))
  else if l = 13 then .load (fun _ => (none, true, BinaryArithmetic.Comparison.initial)) .halt
  else .load (fun _ => (none, false, BinaryArithmetic.Comparison.initial)) .halt

def program : Label → Stmt Stack Label Memory
  | .inl l => Embedded.block parserMap parserLabel (control 0)
      (StateAdapter.block parserState (RequestParser.computer.m l))
  | .inr (.inl (i, l)) => wordCode i l
  | .inr (.inr (.inl strict)) => Embedded.block comparisonMap (compareLabel strict) (returnCompare strict)
      (StateAdapter.block comparisonState (BinaryArithmetic.Comparison.computer.m ()))
  | .inr (.inr (.inr l)) => outside l

abbrev computer : FinTM2 where
  K := Stack
  k₀ := parserMap RequestParser.computer.k₀
  k₁ := parserMap RequestParser.computer.k₁
  Γ _ := Bool
  Λ := Label
  main := parserLabel RequestParser.computer.main
  σ := State
  initialState := (none, false, BinaryArithmetic.Comparison.initial)
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem word_exec (i : Fin 4) :
    ParameterWords.Executes computer.step (wordMap i) (wordLabels i) := by
  refine ⟨?_, ?_, ⟨?_, ?_, ?_⟩⟩ <;> intro state tape <;> rfl

theorem statement_budget (l : Label) : TM2Cost.budget (program l) ≤ 10 := by
  rcases l with l | ((⟨i, l⟩ | (strict | l)))
  · simpa only [program, Embedded.statement_budget, StateAdapter.statement_budget] using RequestParser.statement_budget l
  · fin_cases l <;> simp [program, wordCode, NaturalWords.highestStmt, copyMoveStmt, copyRestoreStmt, TM2Cost.budget]
  · simp only [program, Embedded.statement_budget, StateAdapter.statement_budget, BinaryArithmetic.Comparison.program_budget]
    decide
  · fin_cases l <;> simp [program, outside, positiveStmt, copyMoveStmt, copyRestoreStmt, TM2Cost.budget]

/-- Each retained raw component is normalized by an actual subexecution of
this program, and no other bank field is touched. -/
theorem word_run (i : Fin 4) (memory : Memory) (frame : Stack → List Bool) (raw : List Bool) :
    RunsExactly computer.step
      (cfg (wordLabel i 0) memory (ParameterWords.tapes (wordMap i) frame raw [] [] []))
      (cfg (afterWord i) memory
        (ParameterWords.tapes (wordMap i) frame raw [] (encodeNat (decodeNat raw)) []))
      (4 * raw.length + 5) :=
  ParameterWords.prepare_exact computer.step (wordMap i) (wordLabels i) (word_exec i) memory frame raw

end Counting.Algorithm.KarpLubyRequest.ParameterProgram
