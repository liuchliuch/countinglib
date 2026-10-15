import ComplexCSP.Complexity.TypeStackConcrete
import ComplexCSP.Complexity.CappedIteration

/-! # Total capped stack execution and exact terminating-run recovery

The concrete control transition contains only actual FP callbacks. Fuel and cap
are actual unary polynomial computations. The generic no-cap bridge below uses
proved genuine-run invariants; it is not counted as the completed CSP constructor
until instantiated with its original-instance cap and trace bounds.
-/
namespace ComplexCSP.ComplexityTypeStackExecution
open PlanarHom PlanarHom.Complexity
open MaltsevTypeStack ComplexityTypeStackMachines

variable {A : Type}
def totalize (transition : State A → Option (State A)) (state : State A) : State A :=
  (transition state).getD state

theorem runs_iterate {transition : State A → Option (State A)} {start finish : State A} {count : ℕ}
    (h : Runs transition start finish count) : (totalize transition)^[count] start = finish := by
  induction h with
  | refl => rfl
  | @step start next finish count he hr ih =>
    rw [Function.iterate_succ_apply]
    simpa only [totalize,he,Option.getD_some] using ih

theorem iterate_reached (transition : State A → Option (State A)) (start : State A) (count : ℕ) :
    ∃ k, k ≤ count ∧ Runs transition start ((totalize transition)^[count] start) k := by
  classical
  induction count with
  | zero => exact ⟨0,le_rfl,.refl _⟩
  | succ count ih =>
    obtain ⟨k,hk,hr⟩ := ih
    rw [Function.iterate_succ_apply']
    cases he : transition ((totalize transition)^[count] start) with
    | none =>
      refine ⟨k,by omega,?_⟩
      simpa only [totalize,he,Option.getD_none] using hr
    | some next =>
      refine ⟨k+1,by omega,?_⟩
      have hn := hr.trans (Runs.step he (Runs.refl next))
      simpa only [totalize,he,Option.getD_some] using hn

theorem reached_length_le_of_halt {transition : State A → Option (State A)}
    {start finish : State A} {count : ℕ} (h : Runs transition start finish count)
    (hhalt : transition finish = none) :
    ∀ {other k}, Runs transition start other k → k ≤ count := by
  induction h with
  | refl =>
    intro other k hr
    cases hr with
    | refl => exact le_rfl
    | step he _ => rw [hhalt] at he; contradiction
  | @step start next finish count he hr ih =>
    intro other k hother
    cases hother with
    | refl => omega
    | @step _ next' _ k he' ht =>
      have hsame : next = next' := Option.some.inj (he.symm.trans he')
      subst next'
      have hk := ih hhalt ht
      omega

theorem iterate_after_halt {transition : State A → Option (State A)}
    {start finish : State A} {count : ℕ} (h : Runs transition start finish count)
    (hhalt : transition finish = none) (budget : ℕ) (hb : count ≤ budget) :
    (totalize transition)^[budget] start = finish := by
  obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le hb
  rw [Nat.add_comm,Function.iterate_add_apply,runs_iterate h]
  have hf : totalize transition finish = finish := by simp [totalize,hhalt]
  exact Function.iterate_fixed hf extra

section Concrete
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Fin d → Fin d → Fin d → Fin d)

noncomputable def inputCode :=
  (ComplexityTypeStackConcrete.contextCode basis).prod
    (stateCode (ComplexityCSPMarginalRowBounds.labelEncoding basis d))

noncomputable def run (space time : Polynomial ℕ)
    (p : ComplexityTypeStackConcrete.Context K × State (WeightedMaltsev.RowLabel K d)) :
    State (WeightedMaltsev.RowLabel K d) :=
  ComplexityCappedIteration.runWithBudgets (ComplexityTypeStackConcrete.contextCode basis)
    (stateCode (ComplexityCSPMarginalRowBounds.labelEncoding basis d)) defaultState
    (ComplexityTypeStackConcrete.step L m) space time p

/-- A fully instantiated actual FP bounded type-search program, without any
remaining function/row/reconstruction oracle premise. -/
theorem fp_run (space time : Polynomial ℕ) :
    FP (inputCode (d:=d) basis) (stateCode (ComplexityCSPMarginalRowBounds.labelEncoding basis d))
      (run L basis m space time) :=
  ComplexityCappedIteration.fp_runWithBudgets (ComplexityTypeStackConcrete.contextCode basis)
    (stateCode (ComplexityCSPMarginalRowBounds.labelEncoding basis d)) defaultState
    (ComplexityTypeStackConcrete.step L m) (ComplexityTypeStackConcrete.fp_step L basis m) space time

/-- Source-correct finite trace and bit bounds imply exact recovery by the actual
capped program, even when its chosen fuel exceeds the successful trace length. -/
theorem run_correct (space time : Polynomial ℕ)
    (context : ComplexityTypeStackConcrete.Context K)
    (start finish : State (WeightedMaltsev.RowLabel K d)) (count : ℕ)
    (hr : Runs (fun state => ComplexityTypeStackConcrete.step L m (context,state)) start finish count)
    (hh : ComplexityTypeStackConcrete.step L m (context,finish) = none)
    (ht : count ≤ time.eval ((inputCode (d:=d) basis).encode (context,start)).length)
    (hs : ∀ state k, k ≤ count →
      Runs (fun state => ComplexityTypeStackConcrete.step L m (context,state)) start state k →
      ((stateCode (ComplexityCSPMarginalRowBounds.labelEncoding basis d)).encode state).length ≤
        space.eval ((inputCode (d:=d) basis).encode (context,start)).length) :
    run L basis m space time (context,start) = finish := by
  unfold run
  rw [ComplexityCappedIteration.runWithBudgets_correct]
  · exact iterate_after_halt hr hh _ ht
  · intro i _
    obtain ⟨k,_,hk⟩ := iterate_reached
      (fun state => ComplexityTypeStackConcrete.step L m (context,state)) start i
    exact hs _ k (reached_length_le_of_halt hr hh hk) hk

end Concrete
end ComplexCSP.ComplexityTypeStackExecution
