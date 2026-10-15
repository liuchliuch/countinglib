import Counting.Algorithm.FKT.Orientation
import PlanarHom.OccurrenceKasteleynPeelingMachines
import Counting.FiniteSupport.F1

/-!
# Finite-stack polynomial-time face-table orientation

The source theorem supplies a real TM2 program for the exact table-to-log
function. We choose that witness and apply the shared finite-support compiler.
The resulting computer has finite alphabets on every stack, the same external
codecs, the same time polynomial, and the same transition count on each input.

The input is an encoded literal face table, with binary natural-number labels
and Boolean dart directions. Runtime holds for every table, including repeated
labels and malformed face systems. The separate face-odd guarantee retains the
compatible-dual and listed-face reachability promises. This module does not
extract face data from an ordinary graph or decide geometric planarity.
-/

noncomputable section

namespace Counting.Algorithm.FKT.Orientation

open Turing
open PlanarHom.MultiGraph.Kasteleyn

/-- Fix the actual timed witness for the canonical finite-table solver. -/
def sourceComputer :
    TM2ComputableInPolyTime tableCode.encode logCode.encode orientationLog :=
  Classical.choice fp_computeOrientation

/-- The same public program under the faithful F1 codecs, with every internal
stack alphabet proved finite by actual symbol-support restriction. -/
def computer : Counting.Computation.PolyTime
    tableCode.toFinEncoding logCode.toFinEncoding orientationLog :=
  Counting.Computation.FiniteSupport.toPolyTime sourceComputer

/-- The public computer is exactly the shared compiler's refinement. -/
theorem computer_refined :
    computer.toTM2ComputableInPolyTime =
      Counting.Computation.FiniteSupport.computer sourceComputer := rfl

/-- An actual finite enumeration is available for every typed stack alphabet. -/
@[instance_reducible] def computerAlphabet (k : computer.tm.K) :
    Fintype (computer.tm.Γ k) :=
  computer.finiteAlphabets k

/-- Refinement retains the original time polynomial literally. -/
@[simp] theorem computer_time : computer.time = sourceComputer.time := rfl

/-- Refinement retains each original encoded execution's exact transition count. -/
@[simp] theorem computer_steps (table : Table) :
    (computer.outputsFun table).steps = (sourceComputer.outputsFun table).steps := rfl

/-- Direct execution contract under the unchanged external table and log codecs. -/
def outputs (table : Table) :
    TM2OutputsInTime computer.tm
      ((tableCode.encode table).map computer.inputAlphabet.symm)
      (some ((logCode.encode (orientationLog table)).map computer.outputAlphabet.symm))
      (computer.time.eval (tableCode.encode table).length) :=
  computer.outputsFun table

@[simp] theorem outputs_steps (table : Table) :
    (outputs table).steps = (sourceComputer.outputsFun table).steps := rfl

/-- Erase the supported-symbol subtype proofs from each configuration. -/
def eraseCfg : computer.tm.Cfg → sourceComputer.tm.Cfg :=
  Counting.Computation.FiniteSupport.eraseComputerCfg sourceComputer

/-- Every actual transition commutes with erasure, including the terminal
`none` transition; this is not only a final-output simulation. -/
theorem computer_erase_step (c : computer.tm.Cfg) :
    Option.map eraseCfg (computer.tm.step c) = sourceComputer.tm.step (eraseCfg c) :=
  Counting.Computation.FiniteSupport.computer_erase_step sourceComputer c

/-- The syntax-derived polynomial bounds the encoded output of this computer. -/
def outputLengthPolynomial : Polynomial ℕ :=
  Counting.Computation.PolyTime.outputLengthPolynomial computer

theorem encoded_output_length_le (table : Table) :
    (logCode.encode (orientationLog table)).length ≤
      outputLengthPolynomial.eval (tableCode.encode table).length :=
  Counting.Computation.PolyTime.encoded_output_length_le computer table

/-- Polynomial-time membership is unconditional on raw face-table validity. -/
theorem inFP : Counting.Computation.InFP
    tableCode.toFinEncoding logCode.toFinEncoding orientationLog :=
  ⟨computer⟩

/-- A single public function has the finite-machine witness, the unconditional
literal output bound, and clockwise-odd correctness under the full dual promise. -/
theorem certified_orientationLog :
    Counting.Computation.InFP tableCode.toFinEncoding logCode.toFinEncoding orientationLog ∧
    (∀ table : Table, (orientationLog table).length ≤ table.length) ∧
    ∀ (D : DualIncidence ℕ ℕ) (boundary : Boundaries ℕ ℕ), D.Compatible boundary →
      ∀ (root : ℕ) (fs : List ℕ),
        (∀ f ∈ fs, Relation.ReflTransGen D.Adj root f) →
        fs.Nodup → root ∉ fs → ∀ f ∈ fs,
          FaceOdd (orientation (faceTable boundary fs)) (boundary f) :=
  ⟨inFP, orientationLog_length_le,
    fun D boundary hc root fs hconn hn hr =>
      orientation_faceOdd D boundary hc root fs hconn hn hr⟩

end Counting.Algorithm.FKT.Orientation
