import Counting.Algorithm.FKT.Ising
import PlanarHom.FKTIsingUniformRational

/-!
# Joint graph and coupling input

The field and its rational basis are fixed in the generic computer, while both
graph and coupling are encoded inputs. The rational specialization uses the
literal rational codec on both the parameter and answer. These are typed pair
machines, not a claim about the separately defined arbitrary-raw-word extension.
-/

noncomputable section

namespace Counting.Algorithm.FKT.IsingUniform

open Turing PlanarHom.Complexity

variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}

/-- Actual source witness with graph first and the field parameter second. -/
def sourceComputer (basis : Module.Basis (Fin dimension) ℚ K) :
    TM2ComputableInPolyTime (MixedCode.encoding.prod (numberFieldEncoding basis)).encode
      (numberFieldEncoding basis).encode
      (fun p : MixedCode × K => Ising.value p.2 p.1) :=
  Classical.choice (PlanarHom.FKTIsingUniform.fp_value basis)

/-- A single finite-stack machine accepts the varying coupling as data. -/
def computer (basis : Module.Basis (Fin dimension) ℚ K) :
    Counting.Computation.PolyTime
      (MixedCode.encoding.prod (numberFieldEncoding basis)).toFinEncoding
      (numberFieldEncoding basis).toFinEncoding
      (fun p : MixedCode × K => Ising.value p.2 p.1) :=
  Counting.Computation.FiniteSupport.toPolyTime (sourceComputer basis)

@[simp] theorem computer_time (basis : Module.Basis (Fin dimension) ℚ K) :
    (computer basis).time = (sourceComputer basis).time := rfl

@[simp] theorem computer_steps (basis : Module.Basis (Fin dimension) ℚ K)
    (p : MixedCode × K) :
    ((computer basis).outputsFun p).steps = ((sourceComputer basis).outputsFun p).steps := rfl

/-- The bit-time polynomial charges both the graph and the varying field value. -/
theorem inFP (basis : Module.Basis (Fin dimension) ℚ K) :
    Counting.Computation.InFP
      (MixedCode.encoding.prod (numberFieldEncoding basis)).toFinEncoding
      (numberFieldEncoding basis).toFinEncoding
      (fun p : MixedCode × K => Ising.value p.2 p.1) :=
  ⟨computer basis⟩

namespace Rational

/-- The original specialization converts to and from the literal rational codec. -/
def sourceComputer :
    TM2ComputableInPolyTime (MixedCode.encoding.prod BitEncoding.rat).encode
      BitEncoding.rat.encode (fun p : MixedCode × ℚ => Ising.value p.2 p.1) :=
  Classical.choice PlanarHom.FKTIsingUniform.fp_value_rat

def computer : Counting.Computation.PolyTime
    (MixedCode.encoding.prod BitEncoding.rat).toFinEncoding BitEncoding.rat.toFinEncoding
    (fun p : MixedCode × ℚ => Ising.value p.2 p.1) :=
  Counting.Computation.FiniteSupport.toPolyTime sourceComputer

@[simp] theorem computer_time : computer.time = sourceComputer.time := rfl

@[simp] theorem computer_steps (p : MixedCode × ℚ) :
    (computer.outputsFun p).steps = (sourceComputer.outputsFun p).steps := rfl

theorem inFP : Counting.Computation.InFP
    (MixedCode.encoding.prod BitEncoding.rat).toFinEncoding BitEncoding.rat.toFinEncoding
    (fun p : MixedCode × ℚ => Ising.value p.2 p.1) := ⟨computer⟩

/-- Correctness keeps the original rational specialization's positivity promise. -/
theorem value_eq_partition {g : MixedCode} {bt ut : ℕ} (hg : g.PlanarValid bt ut)
    (ρ : ℚ) (hρ : 0 < ρ) :
    Ising.value ρ g = (g.toMultiGraph hg.1).partition (Ising.matrix ρ) (fun _ => 1) :=
  PlanarHom.FKTIsingUniform.value_eq_partition_rat hg ρ hρ

theorem certified_value :
    Counting.Computation.InFP
      (MixedCode.encoding.prod BitEncoding.rat).toFinEncoding BitEncoding.rat.toFinEncoding
      (fun p : MixedCode × ℚ => Ising.value p.2 p.1) ∧
    ∀ (g : MixedCode) {bt ut : ℕ} (hg : g.PlanarValid bt ut) (ρ : ℚ), 0 < ρ →
      Ising.value ρ g = (g.toMultiGraph hg.1).partition (Ising.matrix ρ) (fun _ => 1) :=
  ⟨inFP, fun _ _ _ hg ρ hρ => value_eq_partition hg ρ hρ⟩

end Rational

end Counting.Algorithm.FKT.IsingUniform
