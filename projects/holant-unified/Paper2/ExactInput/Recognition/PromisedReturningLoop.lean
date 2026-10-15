import Holant.Proofs.Recognition.PhysicalFolds
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.ReturningLoop

/-! A physical returning loop whose cell halts on the proved runtime domain.
The domain index is erased; the machine receives only the encoded current
state. The finite stopping index is used in the run proof, never as input. -/
namespace Paper2.ExactInput.Recognition.PromisedReturningLoop
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.TractChainV1.PhysicalFolds
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
noncomputable section

variable {D A : Type} {ea : Encoding A Bool}
variable (input : D → A) (next : D → D) (keep : D → Bool)
variable (body : Runs ea (pairEncoding encodingBoolBool ea) input
  (fun d => (keep d,input (next d))))

abbrev machine : BinaryCompose.Machine := CommonFieldMachine.ReturningLoop.machine body.machine

theorem run (hio : body.machine.output ≠ body.machine.input)
    (n : ℕ) (d : D)
    (before : ∀ j < n, keep (next^[j] d)=true)
    (last : keep (next^[n] d)=false) :
    ∃ ticks, StackProtocol.RunsExactly (machine input next keep body).computer.step
      (CommonFieldMachine.ReturningLoop.ready body.machine (.inl body.machine.main)
        (.inl body.machine.input) (ea.encode (input d)))
      (haltList (machine input next keep body).computer (ea.encode (input (next^[n+1] d)))) ticks := by
  induction n generalizing d with
  | zero =>
    have hs : keep d=false := last
    let o := body.outputs d
    have h := CommonFieldMachine.ReturningLoop.stop_run body.machine _ _ o.steps (by
      have ho := o.evals_in_steps
      simp only [hs,pairEncoding,encodingBoolBool,encodeBool] at ho
      exact ho)
    exact ⟨_,by simpa only [Nat.zero_add,Function.iterate_one,Function.iterate_zero_apply] using h⟩
  | succ n ih =>
    have hs : keep d=true := before 0 (Nat.zero_lt_succ n)
    let o := body.outputs d
    have first := CommonFieldMachine.ReturningLoop.continue_run body.machine hio _ _ o.steps (by
      have ho := o.evals_in_steps
      simp only [hs,pairEncoding,encodingBoolBool,encodeBool] at ho
      exact ho)
    have hb : ∀ j < n, keep (next^[j] (next d))=true := by
      intro j hj
      simpa only [Function.iterate_succ_apply] using before (j+1) (Nat.succ_lt_succ hj)
    have hl : keep (next^[n] (next d))=false := by
      simpa only [Function.iterate_succ_apply] using last
    obtain ⟨t,rest⟩ := ih (next d) hb hl
    refine ⟨t + (o.steps + 2*(ea.encode (input (next d))).length + 3),?_⟩
    simpa only [Function.iterate_succ_apply] using first.trans rest

/-- This one machine terminates at the first false flag. Neither the stopping
height nor a proof of its existence is encoded in the initial state. -/
theorem outputs_of_first (hio : body.machine.output ≠ body.machine.input)
    (n : ℕ) (d : D)
    (before : ∀ j < n, keep (next^[j] d)=true)
    (last : keep (next^[n] d)=false) :
    ∃ ticks, Nonempty (TM2OutputsInTime (machine input next keep body).computer
      (ea.encode (input d))
      (some (ea.encode (input (next^[n+1] d)))) ticks) := by
  obtain ⟨ticks,h⟩ := run input next keep body hio n d before last
  refine ⟨ticks,⟨{steps := ticks,evals_in_steps := ?_,steps_le_m := le_rfl}⟩⟩
  change StackProtocol.RunsExactly (machine input next keep body).computer.step
    (initList (machine input next keep body).computer (ea.encode (input d)))
    (haltList (machine input next keep body).computer (ea.encode (input (next^[n+1] d)))) ticks
  rw [CommonFieldMachine.ReturningLoop.initial]
  exact h

end
end Paper2.ExactInput.Recognition.PromisedReturningLoop
