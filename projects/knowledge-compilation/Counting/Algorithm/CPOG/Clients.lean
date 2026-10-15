import Counting.Algorithm.CPOG.Bridge
import Counting.Algorithm.CPOG.CNFClients

/-! Concrete supplied POGs exercise actual arrays, polarity, empty conjunctions,
zero declared variables, isolated variables, and end-to-end S1 correctness. -/
namespace Counting.Algorithm.CPOG.Clients
open LeanSAT Model
open FiniteSemantics

/-- Nodes 1 and 2 are variables; node 3 is their decomposable conjunction. -/
def conjunction : Pog where
  elts := #[.var 1, .var 2, .conj 3 #[.mkPos 1, .mkPos 2]]
  wf := by
    intro i
    fin_cases i <;> simp [PogElt.args_decreasing]
    intro j
    fin_cases j <;> decide
  inv := by decide +kernel

/-- A disjoint union of a variable and its negation; the second declared variable is unused. -/
def excludedMiddle : Pog where
  elts := #[.var 1, .disj 2 (.mkPos 1) (.mkNeg 1)]
  wf := Fin.cases (by trivial) (Fin.cases ⟨by decide, by decide⟩ (fun i => i.elim0))
  inv := by decide +kernel

theorem excludedMiddle_count : countRoot excludedMiddle 2 (.mkPos 2) = 4 := by decide +kernel

theorem excludedMiddle_ring :
    ringRoot excludedMiddle (fun _ => (-3 : ℤ)) (.mkPos 2) = 1 := by decide +kernel

/-- The empty conjunction is true even with zero declared variables. -/
def truth : Pog where
  elts := #[.conj 1 #[]]
  wf := by
    intro i
    fin_cases i
    change ∀ j : Fin 0, _
    intro j
    exact j.elim0
  inv := by decide +kernel

theorem conjunction_form : conjunction.toPropForm (.mkPos 3) =
    .conj (.var 1) (.conj (.var 2) .tr) := by decide +kernel

theorem conjunction_partitioned : partitioned (conjunction.toPropForm (.mkPos 3)) := by
  rw [conjunction_form]
  simp [partitioned, PropForm.vars]

theorem conjunction_declared : (conjunction.toPropForm (.mkPos 3)).vars ⊆ declared 3 := by
  rw [conjunction_form]
  decide

/-- The third declared variable is isolated, so the two constrained values give two models. -/
theorem conjunction_count_with_isolated : countRoot conjunction 3 (.mkPos 3) = 2 := by decide +kernel

theorem negative_root_count : countRoot conjunction 3 (.mkNeg 3) = 6 := by decide +kernel

theorem zero_variables_true : countRoot truth 0 (.mkPos 1) = 1 := by decide +kernel

theorem zero_variables_false : countRoot truth 0 (.mkNeg 1) = 0 := by decide +kernel

/-- The normalized complementary weights need not be probabilities. -/
def signedWeight (x : Var) : ℤ := if x = 1 then -2 else if x = 2 then 3 else 7

theorem negative_root_ring : ringRoot conjunction signedWeight (.mkNeg 3) = 7 := by decide +kernel

def notBoth : CNF.Formula 3 := [[⟨0, false⟩, ⟨1, false⟩]]

theorem notBoth_equivalent :
    notBoth.toICnf.toPropFun = (⟦conjunction.toPropForm (.mkNeg 3)⟧ : PropFun Var) := by
  rw [← LeanSAT.Cnf.mk_toPropForm]
  apply PropFun.sound
  intro τ
  rw [CNF.formula_eval, Pog.toPropForm_neg, conjunction_form]
  simp [notBoth, CNF.Formula.eval, CNF.Clause.eval, CNF.Literal.eval,
    CNF.Literal.apply]
  rfl

theorem negative_root_partition :
    countRoot conjunction 3 (.mkNeg 3) = notBoth.toInstance.partition Empty.elim := by
  apply countRoot_eq_partition notBoth conjunction (.mkNeg 3)
  · simpa only [Pog.toPropForm_neg, PropForm.vars] using conjunction_declared
  · simpa only [Pog.toPropForm_neg, partitioned] using conjunction_partitioned
  · exact notBoth_equivalent

theorem negative_root_weighted_partition :
    ringRoot conjunction signedWeight (.mkNeg 3) =
      (notBoth.weightedInstance (fun i => signedWeight (Nat.succPNat i.val))).partition
        Empty.elim := by
  apply ringRoot_eq_partition notBoth conjunction (.mkNeg 3) signedWeight
  · simpa only [Pog.toPropForm_neg, PropForm.vars] using conjunction_declared
  · simpa only [Pog.toPropForm_neg, partitioned] using conjunction_partitioned
  · exact notBoth_equivalent

theorem notBoth_partition_value : notBoth.toInstance.partition Empty.elim = 6 := by
  rw [← negative_root_partition, negative_root_count]

theorem notBoth_weighted_partition_value :
    (notBoth.weightedInstance (fun i => signedWeight (Nat.succPNat i.val))).partition
      Empty.elim = 7 := by
  rw [← negative_root_weighted_partition, negative_root_ring]

end Counting.Algorithm.CPOG.Clients
