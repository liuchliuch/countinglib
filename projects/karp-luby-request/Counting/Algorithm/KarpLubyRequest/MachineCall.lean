import Counting.Algorithm.KarpLubyRequest.StateAdapter

/-!
# Exact calls with explicit before/after banks

This combines the two existing canonical source compilers: finite register
extension and typed stack embedding. Both endpoints must match the full caller
bank, including every untouched stack. The theorem adds no execution assumption
other than the displayed source run and actual caller-code equations.
-/
namespace Counting.Algorithm.KarpLubyRequest.MachineCall
open Turing Holant.Complexity
variable {K J Λ R σ τ ρ : Type} [DecidableEq K] [DecidableEq J]

def block (st : K ↪ J) (labels : Λ → R) (ret : R) (state : σ × τ ≃ ρ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) : TM2.Stmt (fun _ : J => Bool) R ρ :=
  Embedded.block st labels ret (StateAdapter.block state q)

theorem budget (st : K ↪ J) (labels : Λ → R) (ret : R) (state : σ × τ ≃ ρ)
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) :
    TM2Cost.budget (block st labels ret state q) = TM2Cost.budget q := by
  rw [block, Embedded.statement_budget, StateAdapter.statement_budget]

/-- Full-bank relations determine the complete target configuration uniquely. -/
theorem rel_unique (st : K ↪ J) (labels : Λ → R) (ret : R) (frame : J → List Bool)
    (a : TM2.Cfg (fun _ : K => Bool) Λ ρ) (b c : TM2.Cfg (fun _ : J => Bool) R ρ)
    (hb : Embedded.Rel st labels ret frame a b) (hc : Embedded.Rel st labels ret frame a c) :
    b = c := by
  have hl : b.l = c.l := hb.1.trans hc.1.symm
  have hv : b.var = c.var := hb.2.1.trans hc.2.1.symm
  have ht : b.stk = c.stk := by
    funext j
    by_cases h : ∃ k, st k = j
    · obtain ⟨k, rfl⟩ := h
      exact (hb.2.2.1 k).trans (hc.2.2.1 k).symm
    · have ho : ∀ k, j ≠ st k := fun k he => h ⟨k, he.symm⟩
      exact (hb.2.2.2 j ho).trans (hc.2.2.2 j ho).symm
  cases b; cases c; cases hl; cases hv; cases ht; rfl

/-- Exact caller execution; every transition is the compiled source instruction. -/
theorem run (st : K ↪ J) (labels : Λ → R) (ret : R) (state : σ × τ ≃ ρ)
    (source : Λ → TM2.Stmt (fun _ : K => Bool) Λ σ)
    (caller : R → TM2.Stmt (fun _ : J => Bool) R ρ)
    (code : ∀ l, caller (labels l) = block st labels ret state (source l))
    (saved : τ) (frame : J → List Bool)
    (a z : TM2.Cfg (fun _ : K => Bool) Λ σ)
    (start finish : TM2.Cfg (fun _ : J => Bool) R ρ) (time : ℕ)
    (ha : Embedded.Rel st labels ret frame (StateAdapter.cfg state saved a) start)
    (hz : Embedded.Rel st labels ret frame (StateAdapter.cfg state saved z) finish)
    (hr : (fun p => p.bind (TM2.step source))^[time] (some a) = some z) :
    (fun p => p.bind (TM2.step caller))^[time] (some start) = some finish := by
  have hs := StateAdapter.run state source saved a z time hr
  obtain ⟨ending, he, hc⟩ := Embedded.run st labels ret (StateAdapter.program state source)
    caller code (StateAdapter.cfg state saved a) (StateAdapter.cfg state saved z)
    start frame time ha hs
  rw [rel_unique st labels ret frame _ ending finish hc hz] at he
  exact he

/-- Discard the source protocol's singleton memory while keeping all caller
registers. This only renames finite states; no stack instruction is introduced. -/
def unitState (τ : Type) : ((Option Bool × Unit) × τ) ≃ (Option Bool × τ) where
  toFun s := (s.1.1, s.2)
  invFun s := ((s.1, ()), s.2)
  left_inv := by rintro ⟨⟨bit, u⟩, rest⟩; cases u; rfl
  right_inv := by intro s; rfl

end Counting.Algorithm.KarpLubyRequest.MachineCall
