import Counting.Algorithm.KarpLubyRequest.Sampling.TrialProgram

/-! # Explicit physical configurations for the one-trial source -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Trial
open Turing Computability Holant.Complexity StackProtocol

/-- A specification of the eighteen physical stacks, not a machine register. -/
structure Data where
  rows : List Bool := []
  mass : List Bool := []
  random : List Bool := []
  rank : List Bool := []
  remaining : List Bool := []
  row : List Bool := []
  rowMass : List Bool := []
  history : List Bool := []
  clock : List Bool := []
  left : List Bool := []
  right : List Bool := []
  work : List Bool := []
  arithmeticOutput : List Bool := []
  scratch : List Bool := []
  massRow : List Bool := []
  assignment : List Bool := []
  assignmentCopy : List Bool := []
  output : List Bool := []

def Data.tapes (d : Data) : Stack → List Bool
  | .rows => d.rows | .mass => d.mass | .random => d.random | .rank => d.rank
  | .remaining => d.remaining | .row => d.row | .rowMass => d.rowMass | .history => d.history
  | .clock => d.clock | .left => d.left | .right => d.right | .work => d.work
  | .arithmeticOutput => d.arithmeticOutput | .scratch => d.scratch | .massRow => d.massRow
  | .assignment => d.assignment | .assignmentCopy => d.assignmentCopy | .output => d.output

def inputData (rows mass random : List Bool) : Data := { rows := rows, mass := mass, random := random }

def configuration (label : Label) (state : State) (d : Data) : computer.Cfg :=
  ⟨some label, state, d.tapes⟩

def finalConfiguration (rows mass random output : List Bool) : computer.Cfg :=
  ⟨none, initial, ({(inputData rows mass random) with output := output} : Data).tapes⟩

/-- The selector starts from a copied row stream and a physically decoded rank. -/
def selectionData (rows mass suffix : List Bool) (rank : ℕ) : Data :=
  {(inputData rows mass suffix) with rank := encodeNat rank, remaining := rows}

end Counting.Algorithm.KarpLubyRequest.Sampling.Trial
