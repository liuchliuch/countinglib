import Counting.Algorithm.KarpLubyRequest.Sampling.TrialProgram

/-! # The same compiled trial source has a fixed primitive-instruction budget -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Trial
open Turing Holant.Complexity StackProtocol

theorem statement_budget (label : Label) : TM2Cost.budget (program label) ≤ 9 := by
  cases label with
  | fair l =>
    change TM2Cost.budget (MachineCall.block _ _ _ _ _) ≤ _
    rw [MachineCall.budget]
    exact FairTape.statement_budget l
  | selector l =>
    change TM2Cost.budget (MachineCall.block _ _ _ _ _) ≤ _
    rw [MachineCall.budget]
    exact (Selector.statement_budget l).trans (by decide)
  | unrank l =>
    change TM2Cost.budget (MachineCall.block _ _ _ _ _) ≤ _
    rw [MachineCall.budget]
    exact (Unrank.statement_budget l).trans (by decide)
  | owner l =>
    change TM2Cost.budget (MachineCall.block _ _ _ _ _) ≤ _
    rw [MachineCall.budget]
    exact (Owner.statement_budget l).trans (by decide)
  | clear k => change (4 : ℕ) ≤ 9; decide
  | clockMove | clockRestore | rowsMove | rowsRestore | selectStart | selected | ownerStart
  | owned | scaleMove | scaleRestore | scaleStart | scale | done => decide

end Counting.Algorithm.KarpLubyRequest.Sampling.Trial
