import Paper2.Complexity.OracleQueryBounds
import Paper2.Complexity.WitnessCounting
import Holant.Complexity.OracleQueryBounds
import Holant.Complexity.WitnessCounting

/-! The two projects declare the same finite computation interfaces separately.
These translations preserve their actual finite controls, timed executions,
oracle query commands and query bounds. Their common transition semantics is
mathlib's TM2, so no machine simulation or cost assumption is introduced. -/
namespace Paper2.Paper1Proved
open Computability Turing
noncomputable section
set_option backward.isDefEq.respectTransparency false

def oracleCommandIso (K L S : Type) :
    Holant.Complexity.OracleCommand K L S ≃ Paper2.Complexity.OracleCommand K L S where
  toFun | .ordinary s => .ordinary s | .query next => .query next
  invFun | .ordinary s => .ordinary s | .query next => .query next
  left_inv v := by cases v <;> rfl
  right_inv v := by cases v <;> rfl

/-- Every actual instruction and finite control field is copied literally. -/
def oracleMachine (m : Holant.Complexity.OracleMachine) : Paper2.Complexity.OracleMachine where
  K := m.K
  decEqK := m.decEqK
  finiteK := m.finiteK
  inputStack := m.inputStack
  outputStack := m.outputStack
  queryStack := m.queryStack
  answerStack := m.answerStack
  Λ := m.Λ
  finiteLabels := m.finiteLabels
  main := m.main
  σ := m.σ
  finiteState := m.finiteState
  initialState := m.initialState
  program l := oracleCommandIso m.K m.Λ m.σ (m.program l)

theorem oracleMachine_step (m : Holant.Complexity.OracleMachine)
    (oracle : List Bool → List Bool) : (oracleMachine m).step oracle = m.step oracle := by
  funext cfg
  rcases cfg with ⟨label,state,tapes⟩
  cases label with
  | none => rfl
  | some l => cases h : m.program l <;> simp [Paper2.Complexity.OracleMachine.step,
      Holant.Complexity.OracleMachine.step,oracleMachine,oracleCommandIso,h] <;> rfl

def oracleMachine_outputs (m : Holant.Complexity.OracleMachine)
    (oracle : List Bool → List Bool) (a b : List Bool) (t : ℕ)
    (h : m.OutputsInTime oracle a b t) :
    (oracleMachine m).OutputsInTime oracle a b t := by
  unfold Paper2.Complexity.OracleMachine.OutputsInTime
  rw [oracleMachine_step]
  exact h

theorem oracleMachine_run (m : Holant.Complexity.OracleMachine)
    (oracle : List Bool → List Bool) (a : List Bool) (t : ℕ) :
    (oracleMachine m).run oracle a t = m.run oracle a t := by
  unfold Paper2.Complexity.OracleMachine.run Holant.Complexity.OracleMachine.run
  rw [oracleMachine_step]
  rfl

theorem oracleMachine_isQuery (m : Holant.Complexity.OracleMachine) (c : m.Cfg) :
    (oracleMachine m).IsQuery c ↔ m.IsQuery c := by
  constructor
  · rintro ⟨l,next,hl,hcmd⟩
    refine ⟨l,next,hl,?_⟩
    exact (oracleCommandIso m.K m.Λ m.σ).injective hcmd
  · rintro ⟨l,next,hl,hcmd⟩
    refine ⟨l,next,hl,?_⟩
    change oracleCommandIso m.K m.Λ m.σ (m.program l) = _
    rw [hcmd]
    rfl

def polyTime {A B X Y : Type} [Fintype X] [Fintype Y]
    {ea : Encoding A X} {eb : Encoding B Y} {f : A → B}
    (m : Paper2.Complexity.PolyTime ea eb f) : Holant.Complexity.PolyTime ea eb f where
  toTM2ComputableInPolyTime := m.toTM2ComputableInPolyTime
  finiteAlphabets := m.finiteAlphabets

def sharpPWitness {A X : Type} [Fintype X] {ea : Encoding A X} {f : A → ℕ}
    (w : Paper2.Complexity.SharpPWitness ea f) : Holant.Complexity.SharpPWitness ea f where
  witnessLength := w.witnessLength
  accept := w.accept
  verifier := polyTime w.verifier
  counts := w.counts

def oracleReduction {A B C D : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {ec : Encoding C Bool} {ed : Encoding D Bool} {f : A → B} {g : C → D}
    (r : Holant.Complexity.PolyTimeOracleReduction ea eb ec ed f g) :
    Paper2.Complexity.PolyTimeOracleReduction ea eb ec ed f g where
  machine := oracleMachine r.machine
  time := r.time
  correct oracle h a := oracleMachine_outputs _ _ _ _ _ (r.correct oracle h a)

def outputBound {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool} {f : A → B}
    (b : Holant.Complexity.PolynomialOutputBound ea eb f) :
    Paper2.Complexity.PolynomialOutputBound ea eb f where
  bound := b.bound
  length_le := b.length_le

/-- The same program's actual-query certificate transfers with its execution. -/
def controlledReduction {A B C D : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {ec : Encoding C Bool} {ed : Encoding D Bool} {f : A → B} {g : C → D}
    (r : Holant.Complexity.LengthControlledOracleReduction ea eb ec ed f g) :
    Paper2.Complexity.LengthControlledOracleReduction ea eb ec ed f g where
  reduction := oracleReduction r.reduction
  targetOutput := outputBound r.targetOutput
  queryBound := r.queryBound
  safeQuery oracle h a t c run query :=
    r.safeQuery oracle h a t c
      (by change (oracleMachine r.reduction.machine).run oracle (ea.encode a) t = some c at run
          rw [oracleMachine_run] at run
          exact run)
      ((oracleMachine_isQuery _ _).mp query)

end
end Paper2.Paper1Proved
