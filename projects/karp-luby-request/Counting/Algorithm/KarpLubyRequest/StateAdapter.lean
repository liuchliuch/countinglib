import Counting.Algorithm.KarpLubyRequest.Embedded

/-!
# Finite control extension for heterogeneous source calls

The canonical F1 typed compiler carries one untouched register. With the identity
stack/label embedding and a finite-state equivalence, it embeds source control
into a caller's product register without moving any stack or adding transitions.
This is needed to call H1's eighteen-state arithmetic blocks from the six-state
request parser while preserving the other finite registers.
-/
namespace Counting.Algorithm.KarpLubyRequest.StateAdapter
open Turing Holant.Complexity
open PlanarHom.MachineComposition
variable {K Λ σ τ ρ : Type} [DecidableEq K]

def block (e : σ × τ ≃ ρ) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2.Stmt (fun _ : K => Bool) Λ ρ :=
  renameState e (liftStmt (Embedded.embedding (Function.Embedding.refl K)) id q)

def cfg (e : σ × τ ≃ ρ) (saved : τ) (c : TM2.Cfg (fun _ : K => Bool) Λ σ) :
    TM2.Cfg (fun _ : K => Bool) Λ ρ := ⟨c.l, e (c.var, saved), c.stk⟩

theorem stepAux_block (e : σ × τ ≃ ρ) (q : TM2.Stmt (fun _ : K => Bool) Λ σ)
    (state : σ) (saved : τ) (tape : K → List Bool) :
    TM2.stepAux (block e q) (e (state, saved)) tape =
      cfg e saved (TM2.stepAux q state tape) := by
  have he : (Embedded.embedding (Function.Embedding.refl K)).Represents tape tape := by
    intro k; simp [Embedded.embedding]
  have hc := liftStmt_correct (Embedded.embedding (Function.Embedding.refl K)) id q state saved tape tape he
  rw [block, renameState_correct]
  rcases hc with ⟨hl, hv, hs⟩
  have ht : (TM2.stepAux (liftStmt (Embedded.embedding (Function.Embedding.refl K)) id q)
      (state, saved) tape).stk = (TM2.stepAux q state tape).stk := by
    funext k
    simpa [Embedded.embedding] using hs k
  simp only [renameCfgState, cfg, hv, ht]
  congr 1
  simpa using hl

theorem statement_budget (e : σ × τ ≃ ρ) (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (block e q) = TM2Cost.budget q := by
  rw [block, Returning.budget_renameState]
  induction q <;> simp_all [liftStmt, TM2Cost.budget]

def program (e : σ × τ ≃ ρ) (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ) :
    Λ → TM2.Stmt (fun _ : K => Bool) Λ ρ := fun l => block e (source l)

theorem step (e : σ × τ ≃ ρ) (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (saved : τ) (a b : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (h : TM2.step source a = some b) :
    TM2.step (program e source) (cfg e saved a) = some (cfg e saved b) := by
  rcases a with ⟨label, state, tape⟩
  cases label with
  | none => simp [TM2.step] at h
  | some l =>
    have hb : TM2.stepAux (source l) state tape = b := Option.some.inj h
    subst b
    simp only [cfg, program, TM2.step, stepAux_block]

/-- Exact finite executions are preserved, with the supplied extra register
unchanged on every source transition, including its halting transition. -/
theorem run (e : σ × τ ≃ ρ) (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (saved : τ) (a b : TM2.Cfg (fun _ : K => Bool) Λ σ) (time : ℕ)
    (h : (fun p => p.bind (TM2.step source))^[time] (some a) = some b) :
    (fun p => p.bind (TM2.step (program e source)))^[time] (some (cfg e saved a)) =
      some (cfg e saved b) := by
  obtain ⟨ending, hr, he⟩ := simulate_iterations (TM2.step source) (TM2.step (program e source))
    (fun c d => d = cfg e saved c)
    (by intro c d actual hc ha; subst actual; exact ⟨_, step e source saved c d hc, rfl⟩)
    a b (cfg e saved a) time h rfl
  simpa only [he] using hr

end Counting.Algorithm.KarpLubyRequest.StateAdapter
