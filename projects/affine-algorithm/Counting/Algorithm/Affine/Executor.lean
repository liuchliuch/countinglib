import Counting.Algorithm.Affine.Basic
import Holant.Proofs.Tractability.AffineMachine.FiniteCore

/-!
# Eager finite-table compiler and stack execution

Compilation uses the source's stored single- and two-point sample vectors.
Only the final interpretation uses algebraic complex coefficients. In particular,
the compiler itself never runs a summation over all Boolean assignments.
-/
namespace Counting.Algorithm.Affine

open Holant Holant.Tractable
open Holant.LocalDrafts.Tractability

abbrev Program (A : Type) := ProductMachine.Expr (AffineMachine.ScalarCode.Atom A)
abbrev Table := AffineMachine.Dense.Table

/-- Materialize a semantic input's finite residue tables. -/
def table {n : ℕ} (S : Support n) (Q : Phase n) : Table n :=
  AffineMachine.Dense.snapshot S Q

/-- A computable compiler with an explicit scalar-expression accumulator. -/
def compile {A : Type} {n : ℕ} (S : Support n) (Q : Phase n)
    (initial : Program A) : Program A := AffineMachine.FiniteCore.compile (table S Q) initial

/-- Compile with a single externally interpreted scale literal. -/
def program {n : ℕ} (S : Support n) (Q : Phase n) : Program Unit :=
  compile S Q (.literal (.inl ()))

noncomputable def interpret {A : Type} (scales : A → AlgebraicComplex)
    (code : Program A) : AlgebraicComplex := code.eval (AffineMachine.ScalarCode.coefficient scales)

theorem compile_correct {A : Type} {n : ℕ} (scales : A → AlgebraicComplex)
    (S : Support n) (Q : Phase n) (initial : Program A) :
    interpret scales (compile S Q initial) =
      partition (⟨interpret scales initial, S, Q⟩ : Input n) := by
  simpa [interpret, compile, table, AffineMachine.Dense.Table.state] using
    AffineMachine.FiniteCore.compile_correct scales (table S Q) initial

theorem program_correct {n : ℕ} (A : Input n) :
    interpret (fun _ : Unit => A.scale) (program A.support A.phase) = partition A := by
  simpa [program, interpret, ProductMachine.Expr.eval, AffineMachine.ScalarCode.coefficient] using
    compile_correct (fun _ : Unit => A.scale) A.support A.phase (.literal (.inl ()))

/-- Execute emitted bytecode with the actual underflow-checking stack interpreter. -/
theorem run_correct {n : ℕ} (A : Input n) (stack : List AlgebraicComplex) :
    Holant.OneHot.StackProgram.run (AffineMachine.ScalarCode.coefficient (fun _ : Unit => A.scale))
      (program A.support A.phase).code stack =
      some (partition A :: stack,
        (program A.support A.phase).trace (AffineMachine.ScalarCode.coefficient (fun _ : Unit => A.scale))) := by
  rw [ProductMachine.Expr.run_code]
  exact congrArg (fun v => some (v :: stack,
    (program A.support A.phase).trace (AffineMachine.ScalarCode.coefficient (fun _ : Unit => A.scale))))
    (program_correct A)

theorem compile_size {A : Type} {n : ℕ} (S : Support n) (Q : Phase n)
    (initial : Program A) : (compile S Q initial).size ≤ initial.size + 2 * n + 2 :=
  AffineMachine.FiniteCore.compile_size (table S Q) initial

theorem program_length {n : ℕ} (S : Support n) (Q : Phase n) :
    (program S Q).code.length ≤ 2 * n + 3 := by
  rw [ProductMachine.Expr.code_length]
  have h := compile_size S Q (ProductMachine.Expr.literal (.inl ()) : Program Unit)
  change (compile S Q (.literal (.inl ()))).size ≤ 2 * n + 3
  simp only [ProductMachine.Expr.size] at h
  omega

/-- The selected transition count belongs to the same eager compiler. -/
def transitions {n : ℕ} (S : Support n) (Q : Phase n) : ℕ :=
  AffineMachine.FiniteCore.transitions (table S Q)

theorem transitions_le {n : ℕ} (S : Support n) (Q : Phase n) : transitions S Q ≤ n :=
  AffineMachine.FiniteCore.transitions_le _

end Counting.Algorithm.Affine
