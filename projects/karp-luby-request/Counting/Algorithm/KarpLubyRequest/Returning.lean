import Holant.Complexity.MachineReturn
import Holant.Complexity.StackProtocol
import PlanarHom.MachineComposition

/-!
# Returning finite blocks with a shared control representation

H1's returning compiler adds a saved caller register. When no extra register is
needed, F1's existing finite-state renaming removes the singleton Unit factor.
This bridge lets a complete finite block call H1's Option-Bool stack primitives
without duplicating either compiler or storing unbounded data in control.
-/
namespace Counting.Algorithm.KarpLubyRequest.Returning

open Turing
open Holant.Complexity
open PlanarHom.MachineComposition

variable {K J Λ R σ : Type} [DecidableEq K] [DecidableEq J]

def forgetUnit (σ : Type) : σ × Unit ≃ σ where
  toFun := Prod.fst
  invFun s := (s, ())
  left_inv := by intro ⟨s, u⟩; cases u; rfl
  right_inv := by intro s; rfl

/-- Composition of the two unique canonical compiler providers. -/
def block (ret : R) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ :=
  renameState (forgetUnit σ) (MachineReturn.stmt (fun _ : Unit => ret) q)

def cfg (ret : R) (c : TM2.Cfg (fun _ : K => Bool) Λ σ) (frame : J → List Bool) :
    TM2.Cfg (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ :=
  ⟨some (c.l.elim (.inr ret) Sum.inl), c.var, Sum.elim c.stk frame⟩

theorem stepAux_block (ret : R) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (source : K → List Bool) (frame : J → List Bool) :
    TM2.stepAux (block ret q) state (Sum.elim source frame) =
      cfg ret (TM2.stepAux q state source) frame := by
  have h := renameState_correct (forgetUnit σ)
    (MachineReturn.stmt (J := J) (fun _ : Unit => ret) q) (state, ()) (Sum.elim source frame)
  rw [MachineReturn.stepAux_stmt] at h
  exact h

omit [DecidableEq K] in
/-- State equivalence changes no stack instruction or control-flow node. -/
theorem budget_renameState {A B : Type} (e : A ≃ B)
    (q : TM2.Stmt (fun _ : K => Bool) Λ A) :
    TM2Cost.budget (renameState e q) = TM2Cost.budget q := by
  induction q <;> simp_all [renameState, TM2Cost.budget]

theorem budget_block (ret : R) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (block (J := J) ret q) = TM2Cost.budget q := by
  rw [block, budget_renameState, MachineReturn.budget_stmt]

def program (ret : R) (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ) :
    (Λ ⊕ R) → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ
  | .inl label => block ret (source label)
  | .inr label => outside label

theorem step_program_of_step (ret : R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ)
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (frame : J → List Bool)
    (h : TM2.step source c = some d) :
    TM2.step (program ret source outside) (cfg ret c frame) = some (cfg ret d frame) := by
  rcases c with ⟨label, state, stk⟩
  cases label with
  | none => simp [TM2.step] at h
  | some label =>
    have hd : TM2.stepAux (source label) state stk = d := Option.some.inj h
    subst d
    simp only [cfg, Option.elim_some, TM2.step, program, stepAux_block]

/-- Whole actual executions lift with precisely the same transition count.
The canonical finite-run simulation theorem supplies the iteration induction. -/
theorem run_program (ret : R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ)
    (c d : TM2.Cfg (fun _ : K => Bool) Λ σ) (frame : J → List Bool) (time : ℕ)
    (h : (fun p => p.bind (TM2.step source))^[time] (some c) = some d) :
    (fun p => p.bind (TM2.step (program ret source outside)))^[time]
      (some (cfg ret c frame)) = some (cfg ret d frame) := by
  obtain ⟨ending, hr, he⟩ := simulate_iterations (TM2.step source)
    (TM2.step (program ret source outside)) (fun a b => b = cfg ret a frame)
    (by
      intro a a' b hs hb
      subst b
      exact ⟨cfg ret a' frame, step_program_of_step ret source outside a a' frame hs, rfl⟩)
    c d (cfg ret c frame) time h rfl
  simpa only [he] using hr

/-- The generated caller is a finite Boolean-stack machine under exactly the
finite source/caller types given here. -/
abbrev computer [Fintype K] [Fintype J] [Fintype Λ] [Fintype R] [Fintype σ]
    (input output : K) (main : Λ) (initial : σ) (ret : R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (outside : R → TM2.Stmt (fun _ : K ⊕ J => Bool) (Λ ⊕ R) σ) : FinTM2 where
  K := K ⊕ J
  k₀ := .inl input
  k₁ := .inl output
  Γ _ := Bool
  Λ := Λ ⊕ R
  main := .inl main
  σ := σ
  initialState := initial
  m := program ret source outside

end Counting.Algorithm.KarpLubyRequest.Returning
