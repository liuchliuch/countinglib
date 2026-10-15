import Counting.Algorithm.KarpLubyRequest.Preparation.Calls
import Counting.Algorithm.KarpLubyRequest.Preparation.Transfers
import Counting.Algorithm.KarpLubyRequest.Preparation.BankUpdates

/-! Existing canonical sample/group words receive actual retained copies of
mass and the original tape. Only after those transfers is the finite budget
machine invoked. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
set_option backward.isDefEq.respectTransparency false

def budgetWords (samples groups mass tape : List Bool) : Fin 4 → List Bool :=
  ![samples, groups, mass, tape]

theorem budget_ready_update (old : Fin 4 → List Bool) (i : Fin 4) (word : List Bool) :
    Function.update (TapeBudget.Bank.ready old []) (TapeBudget.Bank.original i) word =
      TapeBudget.Bank.ready (Function.update old i word) [] := by
  funext k
  rcases k with k | (k | k)
  · change Function.update (TapeBudget.Bank.ready old []) (TapeBudget.Bank.original i) word
      (TapeBudget.Bank.original k) = Function.update old i word k
    by_cases h : k = i
    · subst k; rw [Function.update_self, Function.update_self]
    · have hn : TapeBudget.Bank.original k ≠ TapeBudget.Bank.original i := fun e => h (Sum.inl.inj e)
      exact (Function.update_of_ne hn _ _).trans (Function.update_of_ne h _ _).symm
  all_goals rfl

/-- The last two tape-budget inputs are populated by real two-pass copies.
The caller's raw source bank and its mass word remain available afterwards. -/
theorem budget_input_copy (d : Data) (memory : Memory)
    (samples groups mass tape : List Bool)
    (hb : d.budget = TapeBudget.Bank.ready (budgetWords samples groups [] []) [])
    (hm : d.mass 2 = mass) (hr : d.tapes tapeSource = tape) (ht : d.scratch = []) :
    RunsExactly computer.step (configuration (.copyMove .mass) (none, memory) d)
      (configuration (.budget (TapeBudget.Bank.own 0)) (none, memory)
        {d with budget := (TapeBudget.Bank.ready (budgetWords samples groups mass tape) [])})
      (2 * (mass.length + tape.length) + 4) := by
  let first : Data := {d with budget :=
    (TapeBudget.Bank.ready (budgetWords samples groups mass []) [])}
  have hzero2 : d.tapes (copyDestination .mass) = [] := by
    change d.budget (TapeBudget.Bank.original 2) = []
    rw [hb]; rfl
  have h0 := copy_run .mass memory d.tapes hzero2 ht
  change RunsExactly computer.step _
    (cfg (.copyMove .tape) memory (Function.update d.tapes (budgetStacks (TapeBudget.Bank.original 2))
      (d.mass 2))) (2 * (d.mass 2).length + 2) at h0
  rw [hm, update_budget, hb, budget_ready_update] at h0
  have e2 : Function.update (budgetWords samples groups [] []) 2 mass =
      budgetWords samples groups mass [] := by funext k; fin_cases k <;> rfl
  rw [e2] at h0
  have hs : first.scratch = [] := ht
  have h1 := copy_run .tape memory first.tapes rfl hs
  have hword : first.tapes (copySource .tape) = tape := hr
  change RunsExactly computer.step _
    (cfg (.budget (TapeBudget.Bank.own 0)) memory
      (Function.update first.tapes (budgetStacks (TapeBudget.Bank.original 3))
        (first.tapes (copySource .tape)))) _ at h1
  rw [hword, update_budget] at h1
  change RunsExactly computer.step _
    (cfg (.budget (TapeBudget.Bank.own 0)) memory
      ({first with budget := (Function.update
        (TapeBudget.Bank.ready (budgetWords samples groups mass []) [])
        (TapeBudget.Bank.original 3) tape)} : Data).tapes) _ at h1
  rw [budget_ready_update] at h1
  have e3 : Function.update (budgetWords samples groups mass []) 3 tape =
      budgetWords samples groups mass tape := by funext k; fin_cases k <;> rfl
  rw [e3] at h1
  convert h0.trans h1 using 1 <;> first | rfl | omega

end
end Counting.Algorithm.KarpLubyRequest.Preparation
