import ComplexCSP.Complexity.ReducedGram
import ComplexCSP.Complexity.GadgetSubstitutionReduction

set_option backward.isDefEq.respectTransparency false

/-! # Literal fixed-path realization of ordinary matrix powers -/
noncomputable section
open Classical
namespace ComplexCSP.PositiveGramPowerGadget
open scoped BigOperators
open ComplexityReducedGram
variable {D K : Type} (A : Matrix D D K)

def edge : Presentation (binaryLanguage A) (Fin 2) :=
  ⟨0,⟨[⟨0,Sum.inl⟩]⟩⟩

def leftPorts : Fin 2 → Fin 2 ⊕ Fin 1 :=
  Fin.cases (Sum.inl 0) (fun _ => Sum.inr 0)
def rightPorts : Fin 2 → Fin 2 ⊕ Fin 1 :=
  Fin.cases (Sum.inr 0) (fun _ => Sum.inl 1)

/-- `path n` has n fresh internal variables and n+1 actual edge constraints. -/
def path : ℕ → Presentation (binaryLanguage A) (Fin 2)
  | 0 => edge A
  | n+1 => (((path n).rename leftPorts).mul ((edge A).rename rightPorts)).marginal

@[simp] theorem edge_table [Fintype D] [CommSemiring K] (a : Fin 2 → D) :
    (edge A).table a=A (a 0) (a 1) := by
  simp [edge,Presentation.table,Instance.partition,Instance.eval,Constraint.eval,binaryLanguage]

@[simp] theorem table_path [Fintype D] [CommSemiring K] (n : ℕ) (a : Fin 2 → D) :
    (path A n).table a=(A^(n+1)) (a 0) (a 1) := by
  induction n generalizing a with
  | zero => simp [path]
  | succ n ih =>
    simp only [path,Presentation.table_marginal,Presentation.table_mul,Presentation.table_rename,
      ih,edge_table]
    simp only [Function.comp_def]
    change (∑ b : Fin 1 → D, (A^(n+1)) (a 0) (b 0)*A (b 0) (a 1)) = _
    conv_rhs => rw [pow_succ,Matrix.mul_apply]
    exact (Equiv.funUnique (Fin 1) D).sum_comp
      (fun z => (A^(n+1)) (a 0) z * A z (a 1))

@[simp] theorem hidden_path (n : ℕ) : (path A n).hidden=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [path,Presentation.marginal,Presentation.mul,Presentation.rename,edge,ih,Nat.add_comm]

@[simp] theorem constraints_path (n : ℕ) : (path A n).inst.constraints.length=n+1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp [path,Presentation.marginal,Presentation.mul,Presentation.rename,Instance.renameHidden,
      Instance.renameBoundary,Instance.hideBoundary,Instance.glue,edge,ih]

section Field
open PlanarHom PlanarHom.Complexity
variable [Fintype D] [Field K] [DecidableEq K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- An actual charged binary-CSP reduction, using the fixed path template.
The source graph may contain loops, parallel edges and isolated vertices. -/
def reduction (n : ℕ) : PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem (binaryLanguage (A^(n+1))) basis)
    (ComplexityCSPCountReduction.partitionProblem (binaryLanguage A) basis) :=
  ComplexityGadgetSubstitution.unrestrictedReduction basis (fun _ => path A n)
    (fun _ a => table_path A n a)

/-- Every specified positive exponent has its literal fixed path compiler. -/
def positiveReduction (N : ℕ) (hN : 0<N) : PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem (binaryLanguage (A^N)) basis)
    (ComplexityCSPCountReduction.partitionProblem (binaryLanguage A) basis) := by
  have he : N-1+1=N := Nat.sub_add_cancel hN
  simpa only [he] using reduction A basis (N-1)

end Field
end ComplexCSP.PositiveGramPowerGadget
