import Counting.Algorithm.KarpLubyRequest.Preparation.Bank

/-! Extensional descriptions of actual single-stack updates in the fixed bank. -/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol

set_option backward.isDefEq.respectTransparency false

theorem update_counts (d : Data) (k : ParameterCountsBank.Stack) (word : List Bool) :
    Function.update d.tapes (countsStacks k) word =
      ({d with counts := Function.update d.counts k word} : Data).tapes := by
  funext j
  rcases j with (j | (j | (j | (j | j)))) | j
  · change Function.update d.tapes (countsStacks k) word (countsStacks j) =
      Function.update d.counts k word j
    by_cases h : j = k
    · subst j
      rw [Function.update_self]
      exact (Function.update_self k word d.counts).symm
    · have hn : countsStacks j ≠ countsStacks k := fun he => h (countsStacks.injective he)
      rw [Function.update_of_ne hn]
      exact (Function.update_of_ne h word d.counts).symm
  all_goals rfl

theorem update_formula (d : Data) (k : Fin 13) (word : List Bool) :
    Function.update d.tapes (formulaStacks k) word =
      ({d with formula := Function.update d.formula k word} : Data).tapes := by
  funext j
  rcases j with (j | (j | (j | (j | j)))) | j
  · rfl
  · change Function.update d.tapes (formulaStacks k) word (formulaStacks j) =
      Function.update d.formula k word j
    by_cases h : j = k
    · subst j
      rw [Function.update_self]
      exact (Function.update_self k word d.formula).symm
    · have hn : formulaStacks j ≠ formulaStacks k := fun he => h (formulaStacks.injective he)
      rw [Function.update_of_ne hn]
      exact (Function.update_of_ne h word d.formula).symm
  all_goals rfl

theorem update_mass (d : Data) (k : Sampling.TotalMass.Stack) (word : List Bool) :
    Function.update d.tapes (massStacks k) word =
      ({d with mass := Function.update d.mass k word} : Data).tapes := by
  funext j
  rcases j with (j | (j | (j | (j | j)))) | j
  · rfl
  · rfl
  · change Function.update d.tapes (massStacks k) word (massStacks j) =
      Function.update d.mass k word j
    by_cases h : j = k
    · subst j
      rw [Function.update_self]
      exact (Function.update_self k word d.mass).symm
    · have hn : massStacks j ≠ massStacks k := fun he => h (massStacks.injective he)
      rw [Function.update_of_ne hn]
      exact (Function.update_of_ne h word d.mass).symm
  all_goals rfl

theorem update_budget (d : Data) (k : TapeBudget.Bank.Stack) (word : List Bool) :
    Function.update d.tapes (budgetStacks k) word =
      ({d with budget := Function.update d.budget k word} : Data).tapes := by
  funext j
  rcases j with (j | (j | (j | (j | j)))) | j
  · rfl
  · rfl
  · rfl
  · change Function.update d.tapes (budgetStacks k) word (budgetStacks j) =
      Function.update d.budget k word j
    by_cases h : j = k
    · subst j
      rw [Function.update_self]
      exact (Function.update_self k word d.budget).symm
    · have hn : budgetStacks j ≠ budgetStacks k := fun he => h (budgetStacks.injective he)
      rw [Function.update_of_ne hn]
      exact (Function.update_of_ne h word d.budget).symm
  all_goals rfl

theorem update_scratch (d : Data) (word : List Bool) :
    Function.update d.tapes scratch word = ({d with scratch := word} : Data).tapes := by
  funext j
  rcases j with (j | (j | (j | (j | j)))) | j <;> first
    | rfl
    | cases j; rfl

theorem update_output (d : Data) (word : List Bool) :
    Function.update d.tapes output word = ({d with output := word} : Data).tapes := by
  funext j
  rcases j with (j | (j | (j | (j | j)))) | j <;> first
    | rfl
    | cases j; rfl

end
end Counting.Algorithm.KarpLubyRequest.Preparation
