import Counting.Algorithm.KarpLubyRequest.Preparation.RawRun

/-! Exact semantic alternatives for the output of the actual raw preparation
machine. These concern the intermediate tag codec, not an FPRAS claim. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

/-- Either the literal zero tag corresponds to the original evaluator's zero
output, or the literal payload names the original accepted request, its
positive mass, exact tape budget, and canonical sample/group words. -/
theorem rawResult_classification (raw : List Bool) :
    (rawResult raw = [false] ∧ ProgramEncoding.evalBits raw = Encoding.encodeOutput 0) ∨
      ∃ r : ProgramEncoding.Request,
        ProgramEncoding.request.decode raw = some r ∧
        Program.ValidRequest r.epsilon r.delta ∧
        0 < Program.totalMass (DNF.normalizeFormula r.problem.formula) ∧
        r.tape.length = Program.requestedBudget r.problem.formula r.epsilon r.delta ∧
        rawResult raw = payload
          (Dense.CellCodec.rows (DenseNormalization.formula r.problem.variableCount r.problem.formula).value)
          (encodeNat (Program.totalMass (DNF.normalizeFormula r.problem.formula)))
          (encodeNat (Program.requestedSamples (DNF.normalizeFormula r.problem.formula) r.epsilon))
          (encodeNat (Program.requestedGroups r.delta)) r.tape := by
  cases hr : ProgramEncoding.request.decode raw with
  | none =>
    exact Or.inl ⟨by simp only [rawResult, hr, Option.elim_none], ProgramEncoding.evalBits_malformed raw hr⟩
  | some r =>
    by_cases hv : Program.ValidRequest r.epsilon r.delta
    · by_cases hm : Program.totalMass (DNF.normalizeFormula r.problem.formula) = 0
      · exact Or.inl ⟨by simp [rawResult, hr, requestResult, hv, problemResult, hm],
          ZeroBranchSpec.evalBits_zero_mass raw r hr hm⟩
      · by_cases ht : r.tape.length = Program.requestedBudget r.problem.formula r.epsilon r.delta
        · exact Or.inr ⟨r, rfl, hv, Nat.pos_of_ne_zero hm, ht, by
            simp [rawResult, hr, requestResult, hv, problemResult, hm, ht]⟩
        · exact Or.inl ⟨by simp [rawResult, hr, requestResult, hv, problemResult, hm, ht],
            ZeroBranchSpec.evalBits_wrong_tape_length raw r hr ht⟩
    · exact Or.inl ⟨by simp [rawResult, hr, requestResult, hv],
        ZeroBranchSpec.evalBits_invalid_parameters raw r hr hv⟩

end
end Counting.Algorithm.KarpLubyRequest.Preparation
