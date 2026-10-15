import Counting.Algorithm.Affine

/-! Kernel-checked executions and a client with repeated occurrences, repeated
ports, a nullary factor and an isolated variable. No native decision axiom is used. -/
namespace Counting.Algorithm.Affine.Clients

open Holant Holant.Tractable Holant.LocalDrafts.Tractability

/-- A unary phase whose coefficient ranges over all four residues. -/
def unary (q : ZMod 4) : Phase 1 :=
  ⟨0, fun _ => q, fun _ _ => 0, fun _ _ _ => Or.inl rfl⟩

def unaryCode (q : ZMod 4) : Program Unit :=
  .mul (.mul (.literal (.inl ())) (.literal (.inr (.inr q)))) (.literal (.inr (.inl 0)))

theorem phase_zero_code : program (AffineSystem.unconstrained 1) (unary 0) = unaryCode 0 := by decide
theorem phase_one_code : program (AffineSystem.unconstrained 1) (unary 1) = unaryCode 1 := by decide
theorem phase_two_cancels : program (AffineSystem.unconstrained 1) (unary 2) = .zero := by decide
theorem phase_three_code : program (AffineSystem.unconstrained 1) (unary 3) = unaryCode 3 := by decide

theorem phase_one_value (s : AlgebraicComplex) :
    interpret (fun _ : Unit => s) (program (AffineSystem.unconstrained 1) (unary 1)) =
      s * (1 + imaginaryUnit) := by
  rw [phase_one_code]
  have h10 : (1 : ZMod 4) ≠ 0 := by decide
  norm_num [interpret, unaryCode, ProductMachine.Expr.eval,
    AffineMachine.ScalarCode.coefficient, AffineMachine.FreePhase.multiplier, h10]

theorem cancellation_value (s : AlgebraicComplex) :
    interpret (fun _ : Unit => s) (program (AffineSystem.unconstrained 1) (unary 2)) = 0 := by
  rw [phase_two_cancels]
  rfl

/-- A zero-coefficient row with right side one must be rejected. -/
def badSupport (n : ℕ) : Support n := ⟨1, fun _ _ => 0, fun _ => 1⟩

theorem bad_row_code : program (badSupport 3) (QuadraticPhase.zero 3) = .zero := by decide

def pinTrue : Support 1 := ⟨1, fun _ _ => 1, fun _ => 1⟩

theorem pin_selected : AffineMachine.Constraint.pivot pinTrue = some (⟨0, by decide⟩, 0) := by decide

theorem pin_phase_code : program pinTrue (unary 3) =
    .mul (.literal (.inl ())) (.literal (.inr (.inl 3))) := by decide

/-- The nontrivial mixed coefficient two yields a parity constraint. -/
def pairPhase : Phase 2 :=
  ⟨0, fun _ => 0, fun _ _ => 2, fun _ _ _ => Or.inr rfl⟩

theorem mixed_code : program (AffineSystem.unconstrained 2) pairPhase = unaryCode 0 := by decide

theorem mixed_value : interpret (fun _ : Unit => (1 : AlgebraicComplex))
    (program (AffineSystem.unconstrained 2) pairPhase) = 2 := by
  rw [mixed_code]
  simp [interpret, unaryCode, ProductMachine.Expr.eval,
    AffineMachine.ScalarCode.coefficient, AffineMachine.FreePhase.multiplier]

theorem zero_scale : interpret (fun _ : Unit => (0 : AlgebraicComplex))
    (program (AffineSystem.unconstrained 2) pairPhase) = 0 := by
  rw [mixed_code]
  simp [interpret, unaryCode, ProductMachine.Expr.eval, AffineMachine.ScalarCode.coefficient]

theorem nullary_code : program (AffineSystem.unconstrained 0) (QuadraticPhase.zero 0) =
    .mul (.literal (.inl ())) (.literal (.inr (.inl 0))) := by decide

inductive Label where
  | pair | phase | scalar
  deriving DecidableEq

noncomputable abbrev language : Language Label where
  arity
    | .pair => 2
    | .phase => 1
    | .scalar => 0
  data
    | .pair => ⟨1, AffineSystem.unconstrained 2, pairPhase⟩
    | .phase => ⟨1, AffineSystem.unconstrained 1, unary 1⟩
    | .scalar => ⟨3, AffineSystem.unconstrained 0, QuadraticPhase.zero 0⟩

/-- Two identical interactions, one repeated-port interaction, a phase and a
nullary scale. Variable 2 is isolated but is still summed over. -/
noncomputable def exampleInstance : Instance language 3 where
  occurrences := [
    ⟨.pair, fun j => .inr (if j = 0 then 0 else 1)⟩,
    ⟨.pair, fun j => .inr (if j = 0 then 0 else 1)⟩,
    ⟨.pair, fun _ => .inr 0⟩,
    ⟨.phase, fun _ => .inr 0⟩,
    ⟨.scalar, Fin.elim0⟩]

private theorem sum_three (f : (Fin 3 → Bool) → AlgebraicComplex) :
    ∑ x, f x =
      f ![false, false, false] + f ![true, false, false] +
      (f ![false, true, false] + f ![true, true, false]) +
      (f ![false, false, true] + f ![true, false, true] +
      (f ![false, true, true] + f ![true, true, true])) := by
  rw [AffineMachine.sum_split, AffineMachine.sum_split, AffineMachine.sum_split]
  simp only [Fintype.sum_unique]
  congr 10

theorem repeated_occurrences_partition : exampleInstance.partition Empty.elim =
    12 * (1 - imaginaryUnit) := by
  rw [Model.OpenInstance.partition, sum_three]
  norm_num [exampleInstance, Model.OpenInstance.eval, Model.Occurrence.eval, Language.semantic,
    language, value, AffineMachine.State.value, affineFormula, pairPhase, unary,
    QuadraticPhase.eval, QuadraticPhase.zero, Fin.sum_univ_succ, bitValue]
  ring

/-- The client's emitted bytecode computes the genuine multi-occurrence S1 sum. -/
theorem repeated_occurrences_executor :
    interpret (fun _ : Unit => (assemble exampleInstance).scale) (instanceProgram exampleInstance) =
      12 * (1 - imaginaryUnit) :=
  (instanceProgram_correct exampleInstance).trans repeated_occurrences_partition

end Counting.Algorithm.Affine.Clients
