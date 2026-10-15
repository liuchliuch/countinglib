import Counting.Algorithm.KarpLubyRequest.FairTape
import Counting.Algorithm.KarpLubyRequest.Sampling.SelectorRun
import Counting.Algorithm.KarpLubyRequest.Sampling.Unrank
import Counting.Algorithm.KarpLubyRequest.Sampling.OwnerRun

/-!
# Actual finite source for one Karp–Luby trial

The retained mass word is physically copied to the fair-bit clock. The interval
selector consumes a real copy of the stored rows, the unranker materializes the
assignment, and the ownership scanner reads the retained occurrence history.
On success, a second physical mass-word scan constructs the dyadic scale. All
temporary stacks are then cleared by ordinary pop loops. The caller's row and
mass words are retained, and its random tape loses exactly the consumed prefix.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Trial
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing

set_option backward.isDefEq.respectTransparency false in
inductive Stack
  | rows | mass | random | rank | remaining | row | rowMass | history | clock
  | left | right | work | arithmeticOutput | scratch | massRow | assignment | assignmentCopy | output
  deriving DecidableEq, Fintype

set_option backward.isDefEq.respectTransparency false in
inductive Label
  | clockMove | clockRestore | fair : Unit → Label
  | rowsMove | rowsRestore | selectStart | selector : Selector.Label → Label
  | selected | unrank : Unrank.Label → Label
  | ownerStart | owner : Owner.Label → Label
  | owned | scaleMove | scaleRestore | scaleStart | scale
  | clear : Fin 14 → Label
  | done
  deriving DecidableEq, Fintype

/-- Shared scratch, two optional arithmetic registers and two Boolean registers.
All four subprogram states embed by permutations of this finite product. -/
abbrev Memory := Option Bool × Option Bool × Bool × Bool
abbrev State := Option Bool × Memory
def initial : State := (none, none, none, false, false)

def fairState : (FairTape.State × (Option Bool × Bool)) ≃ State where
  toFun v := (v.1.1, v.1.2.1, v.2.1, v.1.2.2, v.2.2)
  invFun v := ((v.1, v.2.1, v.2.2.2.1), (v.2.2.1, v.2.2.2.2))
  left_inv := by rintro ⟨⟨a,b,c⟩,d,e⟩; rfl
  right_inv := by rintro ⟨a,b,c,d,e⟩; rfl

def selectorState : (Selector.State × Bool) ≃ State where
  toFun v := (v.1.1, v.1.2.2.1, v.1.2.2.2, v.1.2.1, v.2)
  invFun v := ((v.1, v.2.2.2.1, v.2.1, v.2.2.1), v.2.2.2.2)
  left_inv := by rintro ⟨⟨a,b,c,d⟩,e⟩; rfl
  right_inv := by rintro ⟨a,b,c,d,e⟩; rfl

def ownerState : (RowEval.State × (Option Bool × Option Bool)) ≃ State where
  toFun v := (v.1.1, v.2.1, v.2.2, v.1.2.1, v.1.2.2)
  invFun v := ((v.1, v.2.2.2.1, v.2.2.2.2), v.2.1, v.2.2.1)
  left_inv := by rintro ⟨⟨a,b,c⟩,d,e⟩; rfl
  right_inv := by rintro ⟨a,b,c,d,e⟩; rfl

def unrankState : (Unrank.State × Memory) ≃ State := MachineCall.unitState Memory

def fairStacks : FairTape.Stack ↪ Stack :=
  ⟨fun k => ![.clock, .random, .rank] k,
    by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

def selectorIndex : Selector.Stack → Stack :=
  ![.remaining, .rank, .row, .rowMass, .left, .right, .scratch, .work,
    .arithmeticOutput, .history, .massRow]
private def selectorInverse : Stack → Selector.Stack
  | .remaining => 0 | .rank => 1 | .row => 2 | .rowMass => 3 | .left => 4 | .right => 5
  | .scratch => 6 | .work => 7 | .arithmeticOutput => 8 | .history => 9 | _ => 10
def selectorStacks : Selector.Stack ↪ Stack :=
  ⟨selectorIndex, (show Function.LeftInverse selectorInverse selectorIndex by
    intro k; fin_cases k <;> rfl).injective⟩

def unrankStacks : Unrank.Stack ↪ Stack :=
  ⟨fun k => ![.row, .rank, .massRow, .assignment] k,
    by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

def ownerStacks : Owner.Stack ↪ Stack :=
  ⟨fun k => ![.history, .row, .assignment, .assignmentCopy, .scratch] k,
    by intro a b h; fin_cases a <;> fin_cases b <;> simp_all⟩

/-- A finite static cleanup schedule; its index has fourteen possible values. -/
def clearStack : Fin 14 → Stack :=
  ![.rank, .remaining, .row, .rowMass, .history, .clock, .left, .right,
    .work, .arithmeticOutput, .scratch, .massRow, .assignment, .assignmentCopy]
def clearNext (k : Fin 14) : Label :=
  if h : k.val + 1 < 14 then .clear ⟨k.val + 1, h⟩ else .done

def selectedBranch : Stmt Stack Label Memory :=
  .branch (fun v => v.2.2.2.1)
    (.load (fun _ => initial) (.goto (fun _ => .unrank 0)))
    (.load (fun _ => initial) (.goto (fun _ => .clear 0)))

def ownedBranch : Stmt Stack Label Memory :=
  .branch (fun v => v.2.2.2.2)
    (.load (fun _ => initial) (.goto (fun _ => .scaleMove)))
    (.load (fun _ => initial) (.goto (fun _ => .clear 0)))

def scaleLoop : Stmt Stack Label Memory :=
  .pop .clock (fun v bit => (bit,v.2))
    (.branch (fun v => v.1.isSome)
      (.push .output (fun _ => false)
        (.load (fun _ => initial) (.goto (fun _ => .scale))))
      (.load (fun _ => initial) (.goto (fun _ => .clear 0))))

def program : Label → Stmt Stack Label Memory
  | .clockMove => copyMoveStmt .mass .scratch .clockMove .clockRestore
  | .clockRestore => copyRestoreStmt .mass .clock .scratch .clockRestore (.fair ())
  | .fair l => MachineCall.block fairStacks Label.fair .rowsMove fairState (FairTape.program l)
  | .rowsMove => copyMoveStmt .rows .scratch .rowsMove .rowsRestore
  | .rowsRestore => copyRestoreStmt .rows .remaining .scratch .rowsRestore .selectStart
  | .selectStart => .load (fun _ => initial) (.goto (fun _ => .selector 0))
  | .selector l => MachineCall.block selectorStacks Label.selector .selected selectorState (Selector.program l)
  | .selected => selectedBranch
  | .unrank l => MachineCall.block unrankStacks Label.unrank .ownerStart unrankState (Unrank.program l)
  | .ownerStart => .load (fun _ => (none,none,none,false,true)) (.goto (fun _ => .owner 0))
  | .owner l => MachineCall.block ownerStacks Label.owner .owned ownerState (Owner.program l)
  | .owned => ownedBranch
  | .scaleMove => copyMoveStmt .mass .scratch .scaleMove .scaleRestore
  | .scaleRestore => copyRestoreStmt .mass .clock .scratch .scaleRestore .scaleStart
  | .scaleStart => .push .output (fun _ => true) (.goto (fun _ => .scale))
  | .scale => scaleLoop
  | .clear k => clearStmt (clearStack k) (.clear k) (clearNext k)
  | .done => .load (fun _ => initial) .halt

instance stateFinite : Fintype State := by
  letI : Fintype Selector.State := Selector.computer.σFin
  exact Fintype.ofEquiv (Selector.State × Bool) selectorState

abbrev computer : FinTM2 where
  K := Stack
  k₀ := .random
  k₁ := .output
  Γ _ := Bool
  Λ := Label
  main := .clockMove
  σ := State
  initialState := initial
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem fair_code (l : Unit) :
    program (.fair l) = MachineCall.block fairStacks Label.fair .rowsMove fairState (FairTape.program l) := rfl
theorem selector_code (l : Selector.Label) :
    program (.selector l) = MachineCall.block selectorStacks Label.selector .selected selectorState
      (Selector.program l) := rfl
theorem unrank_code (l : Unrank.Label) :
    program (.unrank l) = MachineCall.block unrankStacks Label.unrank .ownerStart unrankState
      (Unrank.program l) := rfl
theorem owner_code (l : Owner.Label) :
    program (.owner l) = MachineCall.block ownerStacks Label.owner .owned ownerState (Owner.program l) := rfl

end Counting.Algorithm.KarpLubyRequest.Sampling.Trial
