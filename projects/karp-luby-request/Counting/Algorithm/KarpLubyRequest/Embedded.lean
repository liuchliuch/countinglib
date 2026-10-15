import Counting.Algorithm.KarpLubyRequest.Returning

/-!
# Explicit shared-bank calls through the canonical compiler

F1's typed stack/label compiler, finite-state renaming, and halt redirection
supply every generated instruction. This bridge combines their existing
simulation and untouched-stack results for callers that share a stack bank.
-/
namespace Counting.Algorithm.KarpLubyRequest.Embedded
open Turing Holant.Complexity StackProtocol
open PlanarHom.MachineComposition
variable {K J Λ R σ : Type} [DecidableEq K] [DecidableEq J]

def embedding (e : K ↪ J) : StackEmbedding (fun _ : K => Bool) (fun _ : J => Bool) :=
  ⟨e, fun _ => Equiv.refl Bool⟩

def block (e : K ↪ J) (labels : Λ → R) (ret : R)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) : TM2.Stmt (fun _ : J => Bool) R σ :=
  redirectHalt ret (renameState (Returning.forgetUnit σ)
    (liftStmt (embedding e) labels (τ := Unit) q))

/-- A complete caller relation, including every stack outside the source bank. -/
def Rel (e : K ↪ J) (labels : Λ → R) (ret : R) (frame : J → List Bool)
    (a : TM2.Cfg (fun _ : K => Bool) Λ σ) (b : TM2.Cfg (fun _ : J => Bool) R σ) : Prop :=
  b.l = some (a.l.elim ret labels) ∧ b.var = a.var ∧
    (∀ k, b.stk (e k) = a.stk k) ∧
    (∀ j, (∀ k, j ≠ e k) → b.stk j = frame j)

theorem stepAux_block (e : K ↪ J) (labels : Λ → R) (ret : R)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (state : σ)
    (source : K → List Bool) (target : J → List Bool)
    (h : ∀ k, target (e k) = source k) :
    Rel e labels ret target (TM2.stepAux q state source)
      (TM2.stepAux (block e labels ret q) state target) := by
  have he : (embedding e).Represents source target := by
    intro k; simpa [embedding] using h k
  have hc := liftStmt_correct (embedding e) labels q state () source target he
  have hn := renameState_correct (Returning.forgetUnit σ)
    (liftStmt (embedding e) labels (τ := Unit) q) (state, ()) target
  rw [block, redirectHalt_correct]
  change TM2.stepAux _ state target = _ at hn
  rw [hn]
  rcases hc with ⟨hl, hv, hs⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp only [continueCfg]
    simp only [renameCfgState, hl]
    cases (TM2.stepAux q state source).l <;> rfl
  · change (TM2.stepAux (liftStmt (embedding e) labels q) (state, ()) target).var.1 = _
    exact congrArg Prod.fst hv
  · intro k
    change _ = _
    dsimp only [continueCfg]
    simpa [renameCfgState, embedding] using hs k
  · intro j hj
    exact liftStmt_untouched (embedding e) labels q (state, ()) target j hj

theorem statement_budget (e : K ↪ J) (labels : Λ → R) (ret : R)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (block e labels ret q) = TM2Cost.budget q := by
  induction q <;>
    simp_all [block, redirectHalt, renameState, liftStmt, TM2Cost.budget]

/-- A source's finite execution runs in the caller with the same transition
count; all unselected caller stacks are preserved exactly. -/
theorem run (e : K ↪ J) (labels : Λ → R) (ret : R)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (caller : R → TM2.Stmt (fun _ : J => Bool) R σ)
    (code : ∀ l, caller (labels l) = block e labels ret (source l))
    (a z : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (start : TM2.Cfg (fun _ : J => Bool) R σ) (frame : J → List Bool) (time : ℕ)
    (ha : Rel e labels ret frame a start)
    (hr : (fun p => p.bind (TM2.step source))^[time] (some a) = some z) :
    ∃ ending, (fun p => p.bind (TM2.step caller))^[time] (some start) = some ending ∧
      Rel e labels ret frame z ending := by
  apply simulate_iterations (TM2.step source) (TM2.step caller) (Rel e labels ret frame)
    _ a z start time hr ha
  intro c d target hs ht
  rcases c with ⟨lc, state, sourceTape⟩
  cases lc with
  | none => simp [TM2.step] at hs
  | some lc =>
    have hd : TM2.stepAux (source lc) state sourceTape = d := Option.some.inj hs
    subst d
    rcases ht with ⟨hl, hv, hb, hf⟩
    simp only [Option.elim_some] at hl
    have hc := stepAux_block e labels ret (source lc) state sourceTape target.stk hb
    refine ⟨TM2.stepAux (block e labels ret (source lc)) state target.stk, ?_,
      hc.1, hc.2.1, hc.2.2.1, ?_⟩
    · rcases target with ⟨targetLabel, targetState, targetTape⟩
      dsimp at hl hv ⊢
      subst targetLabel targetState
      simp only [TM2.step, code]
    · intro j hj
      exact (hc.2.2.2 j hj).trans (hf j hj)

/-- A caller copy starts directly from its existing bank, preserves the source,
and populates a previously empty destination. Both passes are real transitions. -/
theorem copy_into {τ : Type} (src dst tmp : J) (hsd : src ≠ dst) (hst : src ≠ tmp)
    (hdt : dst ≠ tmp) (step : Cfg J R τ → Option (Cfg J R τ))
    (move restore next : R)
    (hm : ExecutesAt step move (copyMoveStmt src tmp move restore))
    (hr : ExecutesAt step restore (copyRestoreStmt src dst tmp restore next))
    (memory : τ) (frame : J → List Bool) (hd : frame dst = []) (ht : frame tmp = []) :
    RunsExactly step (cfg move memory frame)
      (cfg next memory (Function.update frame dst (frame src))) (2 * (frame src).length + 2) := by
  have h := copy_exact_frame src dst tmp hsd hst hdt step move restore next hm hr memory frame
    (frame src) []
  have a : tapes3 frame src dst tmp (frame src) [] [] = frame := by
    clear hm hr h
    funext k
    by_cases h0 : k = src <;> by_cases h1 : k = dst <;> by_cases h2 : k = tmp <;>
      simp_all [tapes3, Function.update_apply]
  have b : tapes3 frame src dst tmp (frame src) (frame src) [] =
      Function.update frame dst (frame src) := by
    clear hm hr h
    funext k
    by_cases h0 : k = src <;> by_cases h1 : k = dst <;> by_cases h2 : k = tmp <;>
      simp_all [tapes3, Function.update_apply]
  simpa only [List.append_nil, a, b, Nat.mul_add, Nat.mul_one] using h

end Counting.Algorithm.KarpLubyRequest.Embedded
