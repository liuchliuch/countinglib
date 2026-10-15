import Counting.Algorithm.KarpLubyRequest.Sampling.TrialRandom
import Counting.Algorithm.KarpLubyRequest.Sampling.TrialFlow

/-! # A complete finite, physically clocked Karp–Luby trial -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Trial
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

def runTime (rows : List RowSemantics.Cells) (mass bits suffix : List Bool) : ℕ :=
  3 * mass.length + 2 * (Dense.CellCodec.rows rows).length + 6 +
    selectedTime rows mass suffix (BinaryArithmetic.value bits.reverse)

/-- Source execution from the prepared retained rows/mass and an actual fair-bit
prefix. Every copy, arithmetic call, ownership check, and cleanup runs here. -/
theorem run_exact (n : ℕ) (rows : List RowSemantics.Cells) (mass bits suffix : List Bool)
    (hlen : ∀ row ∈ rows, row.length = n) (hbits : bits.length = mass.length) :
    RunsExactly computer.step
      (configuration .clockMove initial (inputData (Dense.CellCodec.rows rows) mass (bits ++ suffix)))
      (finalConfiguration (Dense.CellCodec.rows rows) mass suffix
        (encodeNat (value mass (SelectorSpec.seek rows (BinaryArithmetic.value bits.reverse) []))))
      (runTime rows mass bits suffix) := by
  have h1 := random_prefix (Dense.CellCodec.rows rows) mass bits suffix hbits
  have h2 := select_to_halt n rows mass suffix (BinaryArithmetic.value bits.reverse) hlen
  convert h1.trans h2 using 1 <;> dsimp only [runTime] <;> omega

/-- On the canonical mass actually computed by the preceding row scanner, the
finite trial returns the original estimator's integer numerator contribution. -/
theorem run_original (n : ℕ) (rows : List RowSemantics.Cells) (bits suffix : List Bool)
    (hlen : ∀ row ∈ rows, row.length = n)
    (hbits : bits.length = (encodeNat (TotalMass.rowSum rows)).length) :
    RunsExactly computer.step
      (configuration .clockMove initial
        (inputData (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (bits ++ suffix)))
      (finalConfiguration (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) suffix
        (encodeNat (Program.trial (rows.map (DenseNormalization.denote n))
          (BinaryArithmetic.value bits.reverse))))
      (runTime rows (encodeNat (TotalMass.rowSum rows)) bits suffix) := by
  have hr := run_exact n rows (encodeNat (TotalMass.rowSum rows)) bits suffix hlen hbits
  have hv : value (encodeNat (TotalMass.rowSum rows))
      (SelectorSpec.seek rows (BinaryArithmetic.value bits.reverse) []) =
      Program.trial (rows.map (DenseNormalization.denote n)) (BinaryArithmetic.value bits.reverse) :=
    TrialSpec.trialValue_original n rows _ hlen
  rw [hv] at hr
  exact hr

theorem primitive_run (n : ℕ) (rows : List RowSemantics.Cells) (bits suffix : List Bool)
    (hlen : ∀ row ∈ rows, row.length = n)
    (hbits : bits.length = (encodeNat (TotalMass.rowSum rows)).length) :
    (Primitive.run program (runTime rows (encodeNat (TotalMass.rowSum rows)) bits suffix)
      (some (configuration .clockMove initial
        (inputData (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (bits ++ suffix))))).2 =
      some (finalConfiguration (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) suffix
        (encodeNat (Program.trial (rows.map (DenseNormalization.denote n))
          (BinaryArithmetic.value bits.reverse)))) ∧
    (Primitive.run program (runTime rows (encodeNat (TotalMass.rowSum rows)) bits suffix)
      (some (configuration .clockMove initial
        (inputData (Dense.CellCodec.rows rows) (encodeNat (TotalMass.rowSum rows)) (bits ++ suffix))))).1 ≤
      9 * runTime rows (encodeNat (TotalMass.rowSum rows)) bits suffix :=
  Primitive.execution_cost program 9 statement_budget _ _ _ (run_original n rows bits suffix hlen hbits)

theorem advance_length (bit : Bool) (word : List Bool) :
    (FairTape.advance bit word).length ≤ word.length + 1 := by
  cases word <;> cases bit <;> simp [FairTape.advance]

theorem collect_length (bits word : List Bool) :
    (FairTape.collect bits word).length ≤ bits.length + word.length := by
  induction bits generalizing word with
  | nil => simp only [FairTape.collect, List.length_nil, Nat.zero_add, le_refl]
  | cons bit bits ih =>
    have ht := ih (FairTape.advance bit word)
    have ha := advance_length bit word
    simp only [FairTape.collect, List.length_cons]
    omega

/-- The actual canonical rank cannot be wider than the consumed fair prefix. -/
theorem rank_length (bits : List Bool) :
    (encodeNat (BinaryArithmetic.value bits.reverse)).length ≤ bits.length := by
  rw [← FairTape.collect_encode]
  simpa only [List.length_nil, Nat.add_zero] using collect_length bits []

end Counting.Algorithm.KarpLubyRequest.Sampling.Trial
