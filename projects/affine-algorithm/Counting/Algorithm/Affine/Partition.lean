import Counting.Algorithm.Affine.Executor
import Counting.Model.Basic
import Holant.Proofs.Tractability.AffineMachine.Assembly

/-!
# Affine occurrence instances

Every local table is supplied by finite affine data, not by an oracle or a
correctness premise. Placement uses the ordered scope exactly as given, including
repeated variables. Collection traverses the occurrence list without deduplication.
-/
namespace Counting.Algorithm.Affine

open Holant Holant.Tractable Counting.Model Holant.LocalDrafts.Tractability

/-- Finite affine presentations of each signature in a possibly infinite label type.
A particular instance still contains only a finite occurrence list. -/
structure Language (ι : Type) where
  arity : ι → ℕ
  data : (i : ι) → Input (arity i)

noncomputable abbrev Language.semantic {ι : Type} (L : Language ι) :
    Model.Language Bool AlgebraicComplex ι where
  arity := L.arity
  value i := value (L.data i)

/-- Closed S1 instances; `Fin n` retains every isolated variable. -/
abbrev Instance {ι : Type} (L : Language ι) (n : ℕ) :=
  Model.OpenInstance L.semantic Empty (Fin n)

/-- Remove only the impossible boundary tag; no variable identifications are added. -/
def closedScope {n : ℕ} : Empty ⊕ Fin n → Fin n := Sum.elim Empty.elim id

/-- Pull back each local presentation and multiply in list order. -/
noncomputable def assemble {ι : Type} {L : Language ι} {n : ℕ} (I : Instance L n) : Input n :=
  AffineMachine.Assembly.collect (I.occurrences.map fun c =>
    AffineMachine.Assembly.place (m := L.arity c.symbol) (fun j => closedScope (c.scope j))
      (L.data c.symbol))

theorem assemble_value {ι : Type} {L : Language ι} {n : ℕ}
    (I : Instance L n) (x : Fin n → Bool) : value (assemble I) x = I.eval Empty.elim x := by
  change (assemble I).value x = I.eval Empty.elim x
  rw [assemble, AffineMachine.Assembly.collect_value]
  simp only [Model.OpenInstance.eval, List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  dsimp only [Function.comp_def]
  rw [AffineMachine.Assembly.place_value]
  change value (L.data c.symbol) (fun j => x (closedScope (c.scope j))) =
    value (L.data c.symbol) (Sum.elim Empty.elim x ∘ c.scope)
  congr 1
  funext j
  cases h : c.scope j with
  | inl e => exact Empty.elim e
  | inr k => simp [h, closedScope]

theorem assemble_partition {ι : Type} {L : Language ι} {n : ℕ} (I : Instance L n) :
    partition (assemble I) = I.partition Empty.elim := by
  apply Finset.sum_congr rfl
  intro x hx
  exact assemble_value I x

/-- The common finite compiler receives the assembled support and phase. -/
noncomputable def instanceProgram {ι : Type} {L : Language ι} {n : ℕ}
    (I : Instance L n) : Program Unit := program (assemble I).support (assemble I).phase

theorem instanceProgram_correct {ι : Type} {L : Language ι} {n : ℕ}
    (I : Instance L n) :
    interpret (fun _ : Unit => (assemble I).scale) (instanceProgram I) = I.partition Empty.elim :=
  (program_correct (assemble I)).trans (assemble_partition I)

/-- Full bytecode execution returns the S1 partition value and preserves the stack suffix. -/
theorem instance_run_correct {ι : Type} {L : Language ι} {n : ℕ}
    (I : Instance L n) (stack : List AlgebraicComplex) :
    Holant.OneHot.StackProgram.run
      (AffineMachine.ScalarCode.coefficient (fun _ : Unit => (assemble I).scale))
      (instanceProgram I).code stack =
      some (I.partition Empty.elim :: stack,
        (instanceProgram I).trace
          (AffineMachine.ScalarCode.coefficient (fun _ : Unit => (assemble I).scale))) := by
  simpa only [instanceProgram, assemble_partition] using run_correct (assemble I) stack

/-- Assembly preserves each row occurrence, including duplicate equations. -/
theorem assemble_rows {ι : Type} {L : Language ι} {n : ℕ} (I : Instance L n) :
    (assemble I).support.rows =
      (I.occurrences.map fun c => (L.data c.symbol).support.rows).sum := by
  rw [assemble, AffineMachine.Assembly.collect_rows]
  simp only [List.map_map]
  rfl

theorem instance_program_length {ι : Type} {L : Language ι} {n : ℕ} (I : Instance L n) :
    (instanceProgram I).code.length ≤ 2 * n + 3 := program_length _ _

end Counting.Algorithm.Affine
