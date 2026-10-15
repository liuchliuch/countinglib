import Counting.Algorithm.KarpLubyRequest.Dense.CellCodec
import Counting.Algorithm.KarpLubyRequest.ParameterWords
import Holant.Complexity.GraphPreprocessing.Primitive

/-!
# Actual allocation of a dense Boolean row

A two-pass copy preserves the original unary variable word. The scan consumes
one physical symbol per transition and pushes two false symbols, allocating one
unassigned cell for every declared variable, regardless of the unary bit values.
The exact returning execution leaves both scratch stacks empty and preserves all
other caller stacks. There is no natural counter in finite control.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Allocate
open Turing Computability Holant.Complexity StackProtocol
open Turing.TM2.Stmt

variable {K Λ τ : Type} [DecidableEq K]

/-- Original unary word, disposable copy, dense output, copy scratch. -/
abbrev Stacks (K : Type) := Fin 4 ↪ K

structure Labels (Λ : Type) where
  copy : Λ
  restore : Λ
  scan : Λ
  next : Λ

def tapes (st : Stacks K) (frame : K → List Bool)
    (original work output scratch : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update frame (st 0) original)
    (st 1) work) (st 2) output) (st 3) scratch

@[simp] theorem tapes_at (st : Stacks K) (frame : K → List Bool)
    (original work output scratch : List Bool) (i : Fin 4) :
    tapes st frame original work output scratch (st i) =
      (![original, work, output, scratch] : Fin 4 → List Bool) i := by
  fin_cases i <;> simp [tapes, st.injective.eq_iff]

theorem tapes_other (st : Stacks K) (frame : K → List Bool)
    (original work output scratch : List Bool) (k : K) (h : ∀ i : Fin 4, k ≠ st i) :
    tapes st frame original work output scratch k = frame k := by
  simp [tapes, Function.update_apply, h]

/-- The input symbol's value is irrelevant; its physical presence creates a cell. -/
def scanStmt (work output : K) (loop next : Λ) : Stmt K Λ τ :=
  pop work (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (push output (fun _ => false) (push output (fun _ => false)
        (load (fun v => (none, v.2)) (goto (fun _ => loop)))))
      (load (fun v => (none, v.2)) (goto (fun _ => next))))

omit [DecidableEq K] in
@[simp] theorem scanStmt_budget (work output : K) (loop next : Λ) :
    TM2Cost.budget (scanStmt (τ := τ) work output loop next) = 6 := rfl

structure Executes (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (st : Stacks K) (lab : Labels Λ) : Prop where
  copy : ExecutesAt step lab.copy (copyMoveStmt (st 0) (st 3) lab.copy lab.restore)
  restore : ExecutesAt step lab.restore
    (copyRestoreStmt (st 0) (st 1) (st 3) lab.restore lab.scan)
  scan : ExecutesAt step lab.scan (scanStmt (st 1) (st 2) lab.scan lab.next)

private theorem as_copy (st : Stacks K) (frame : K → List Bool)
    (original work output scratch : List Bool) :
    tapes st frame original work output scratch =
      tapes3 (Function.update frame (st 2) output) (st 0) (st 1) (st 3)
        original work scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, tapes3, Function.update_apply, st.injective.eq_iff]

section Returning
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (st : Stacks K) (lab : Labels Λ)
variable (exec : Executes step st lab) (memory : τ) (frame : K → List Bool)
include exec

theorem scan_cons (original : List Bool) (bit : Bool) (work output scratch : List Bool) :
    step (cfg lab.scan memory (tapes st frame original (bit :: work) output scratch)) =
      some (cfg lab.scan memory (tapes st frame original work (false :: false :: output) scratch)) := by
  rw [cfg, exec.scan]
  simp [scanStmt, TM2.stepAux, cfg, tapes, st.injective.eq_iff]
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [Function.update_apply, st.injective.eq_iff]

theorem scan_nil (original output scratch : List Bool) :
    step (cfg lab.scan memory (tapes st frame original [] output scratch)) =
      some (cfg lab.next memory (tapes st frame original [] output scratch)) := by
  rw [cfg, exec.scan]
  simp [scanStmt, TM2.stepAux, cfg, tapes, st.injective.eq_iff]

/-- One complete scan, including the final empty-stack test. -/
theorem scan_exact (original work output scratch : List Bool) :
    RunsExactly step (cfg lab.scan memory (tapes st frame original work output scratch))
      (cfg lab.next memory
        (tapes st frame original [] (List.replicate (2 * work.length) false ++ output) scratch))
      (work.length + 1) := by
  induction work generalizing output with
  | nil => simpa using runsExactly_one (scan_nil step st lab exec memory frame original output scratch)
  | cons bit work ih =>
    have h := (runsExactly_one (scan_cons step st lab exec memory frame original bit work output scratch)).trans
      (ih (false :: false :: output))
    have he : List.replicate (2 * work.length) false ++ false :: false :: output =
        List.replicate (2 * (bit :: work).length) false ++ output := by
      rw [List.length_cons, Nat.mul_succ, List.replicate_add, List.append_assoc]
      rfl
    rw [he] at h
    exact h

/-- Full real allocation: two physical copy passes, then a physical cell scan.
The dense word is prepended to an arbitrary existing output suffix. -/
theorem allocate_exact (original output : List Bool) :
    RunsExactly step (cfg lab.copy memory (tapes st frame original [] output []))
      (cfg lab.next memory (tapes st frame original []
        (CellCodec.encode (Counting.Algorithm.KarpLubyMachine.DenseNormalization.allocate original.length).value
          ++ output) []))
      (3 * original.length + 3) := by
  have hc : RunsExactly step (cfg lab.copy memory (tapes st frame original [] output []))
      (cfg lab.scan memory (tapes st frame original original output []))
      (2 * (original.length + 1)) := by
    simpa only [← as_copy, List.append_nil] using
      copy_exact_frame (st 0) (st 1) (st 3)
        (fun h => by have := st.injective h; contradiction)
        (fun h => by have := st.injective h; contradiction)
        (fun h => by have := st.injective h; contradiction)
        step lab.copy lab.restore lab.scan exec.copy exec.restore memory
        (Function.update frame (st 2) output) original []
  have hs := scan_exact step st lab exec memory frame original original output []
  rw [← CellCodec.encode_allocate original.length] at hs
  convert hc.trans hs using 1 <;> omega

end Returning

/-- Four actual Boolean stacks and four finite labels instantiate the protocol. -/
def localStacks : Stacks (Fin 4) := ⟨id, fun _ _ h => h⟩
def localLabels : Labels (Fin 4) := ⟨0, 1, 2, 3⟩

def program (label : Fin 4) : Stmt (Fin 4) (Fin 4) Unit :=
  if label = 0 then copyMoveStmt 0 3 0 1
  else if label = 1 then copyRestoreStmt 0 1 3 1 2
  else if label = 2 then scanStmt 1 2 2 3
  else halt

abbrev computer : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 2
  Γ _ := Bool
  Λ := Fin 4
  main := 0
  σ := Option Bool × Unit
  initialState := (none, ())
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem statement_budget (label : Fin 4) : TM2Cost.budget (program label) ≤ 6 := by
  fin_cases label <;> decide

theorem computer_executes : Executes computer.step localStacks localLabels := by
  constructor <;> intro state tape <;> rfl

theorem cfg_init (original : List Bool) :
    cfg (0 : Fin 4) () (tapes localStacks (fun _ => []) original [] [] []) =
      initList computer original := by
  unfold cfg initList
  congr 1
  funext k
  fin_cases k <;> rfl

/-- The concrete finite computer preserves the original variable word. -/
theorem computer_returns (original : List Bool) :
    RunsExactly computer.step (initList computer original)
      (cfg (3 : Fin 4) () (tapes localStacks (fun _ => []) original []
        (CellCodec.encode (Counting.Algorithm.KarpLubyMachine.DenseNormalization.allocate original.length).value) []))
      (3 * original.length + 3) := by
  simpa only [localLabels, cfg_init, List.append_nil] using
    allocate_exact computer.step localStacks localLabels computer_executes () (fun _ => []) original []

/-- The primitive interpreter charges the very same returning execution. -/
theorem computer_primitive_cost (original : List Bool) :
    (GraphPreprocessing.Primitive.run program (3 * original.length + 3)
      (some (initList computer original))).2 =
      some (cfg (3 : Fin 4) () (tapes localStacks (fun _ => []) original []
        (CellCodec.encode (Counting.Algorithm.KarpLubyMachine.DenseNormalization.allocate original.length).value) [])) ∧
    (GraphPreprocessing.Primitive.run program (3 * original.length + 3)
      (some (initList computer original))).1 ≤ 6 * (3 * original.length + 3) :=
  GraphPreprocessing.Primitive.execution_cost program 6 statement_budget _ _ _ (computer_returns original)

end Counting.Algorithm.KarpLubyRequest.Dense.Allocate
