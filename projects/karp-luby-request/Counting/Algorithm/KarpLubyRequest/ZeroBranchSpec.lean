import Counting.Algorithm.KarpLubyRequest.Contract

/-!
# The unchanged zero-output branches on arbitrary raw requests

The final R1 byte output is rational zero on malformed decoding, invalid
parameters or a wrong tape length. A successfully parsed zero-mass formula also
has value zero for every tape and every parameter value. This last value theorem
does not identify internal parser/gate status flags or remove a machine gate;
callers may retain the exact valid, wrong-length and zero-mass branches.
No canonical representation premise is imposed on the raw request.
-/
namespace Counting.Algorithm.KarpLubyRequest.ZeroBranchSpec
open Counting.Algorithm.KarpLuby

/-- Every trial of a zero-mass family vanishes, for all sample/group counts. -/
theorem estimate_zero_mass {n : ℕ} (cs : List (DNF.Clause n)) (s g : ℕ)
    (hm : Program.totalMass cs = 0)
    (tape : CoinTape (Program.randomBitBudget cs s g)) :
    Program.estimate cs s g tape = 0 := by
  unfold Program.estimate
  apply median_all_zero
  intro i
  simp [Program.groupAverage, Program.naturalAverage, Program.trial_of_zero_mass cs hm]

theorem run_zero_mass {n : ℕ} (f : DNF.Formula n) (epsilon delta : ℚ)
    (hm : Program.totalMass (DNF.normalizeFormula f) = 0)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    Program.run f epsilon delta tape = 0 :=
  estimate_zero_mass (DNF.normalizeFormula f) _ _ hm tape

/-- This value equation needs neither valid parameters nor an accepted tape length. -/
theorem evalRequest_zero_mass (r : ProgramEncoding.Request)
    (hm : Program.totalMass (DNF.normalizeFormula r.problem.formula) = 0) :
    ProgramEncoding.evalRequest r = 0 := by
  unfold ProgramEncoding.evalRequest
  split_ifs
  · exact run_zero_mass r.problem.formula r.epsilon r.delta hm _
  · rfl
  · rfl

/-- Successful raw decoding is sufficient; the original word need not be canonical. -/
theorem evalBits_zero_mass (raw : List Bool) (r : ProgramEncoding.Request)
    (hr : ProgramEncoding.request.decode raw = some r)
    (hm : Program.totalMass (DNF.normalizeFormula r.problem.formula) = 0) :
    ProgramEncoding.evalBits raw = Encoding.encodeOutput 0 := by
  simp only [ProgramEncoding.evalBits, hr]
  rw [evalRequest_zero_mass r hm]

/-- The actual three-field parser may supply its factorized decoding evidence. -/
theorem split_validate_zero_mass (raw : List Bool) (fields : Contract.Fields)
    (r : ProgramEncoding.Request) (hs : Contract.split raw = some fields)
    (hr : Contract.validate fields = some r)
    (hm : Program.totalMass (DNF.normalizeFormula r.problem.formula) = 0) :
    ProgramEncoding.evalBits raw = Encoding.encodeOutput 0 := by
  apply evalBits_zero_mass raw r _ hm
  rw [← Contract.decode_eq]
  simp [Contract.decode, hs, hr]

/-- Preserve the exact invalid-parameter branch of the original raw evaluator. -/
theorem evalBits_invalid_parameters (raw : List Bool) (r : ProgramEncoding.Request)
    (hr : ProgramEncoding.request.decode raw = some r)
    (hv : ¬ Program.ValidRequest r.epsilon r.delta) :
    ProgramEncoding.evalBits raw = Encoding.encodeOutput 0 := by
  simp only [ProgramEncoding.evalBits, hr]
  rw [ProgramEncoding.evalRequest_invalid r hv]

/-- Preserve the exact wrong-length gate, independently of the zero-mass shortcut. -/
theorem evalBits_wrong_tape_length (raw : List Bool) (r : ProgramEncoding.Request)
    (hr : ProgramEncoding.request.decode raw = some r)
    (ht : r.tape.length ≠ Program.requestedBudget r.problem.formula r.epsilon r.delta) :
    ProgramEncoding.evalBits raw = Encoding.encodeOutput 0 := by
  simp only [ProgramEncoding.evalBits, hr]
  rw [ProgramEncoding.evalRequest_wrong_length r ht]

end Counting.Algorithm.KarpLubyRequest.ZeroBranchSpec
