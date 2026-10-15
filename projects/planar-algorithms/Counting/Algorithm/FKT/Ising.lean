import PlanarHom.FKTIsingCorrectness
import Counting.FiniteSupport.F1

/-!
# Typed Ising evaluation on finite-stack machines

The canonical program computes its Fisher graph, orientation, reference sign,
Pfaffian, and normalization from the ordinary `MixedCode` input. This interface
refines its actual timed machine to finite symbol support, preserving the
external codecs, time polynomial, and exact transition counts.

Runtime is unconditional on typed inputs. Partition correctness uses the
original planar promise and `1 + φ ρ ≠ 0`. The represented field, basis, and
coupling are fixed parameters of the machine; graph size varies with the input.
-/

noncomputable section

namespace Counting.Algorithm.FKT.Ising

open Turing PlanarHom.Complexity

variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}

/-- Equal spins have weight 1 and unequal spins have weight `ρ`. -/
abbrev matrix (ρ : K) : Matrix Bool Bool K := PlanarHom.FKTIsingMachines.matrix ρ

/-- The canonical calibrated Fisher matching-value program. -/
abbrev matchingValue (ρ : K) : MixedCode → K :=
  PlanarHom.FKTIsingMachines.matchingValue ρ

/-- The complete ordinary-input numeric Ising program. -/
abbrev value (ρ : K) : MixedCode → K := PlanarHom.FKTIsingMachines.value ρ

/-- Fix the actual source witness, without assumptions on the input graph. -/
def sourceComputer (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K) :
    TM2ComputableInPolyTime MixedCode.encoding.encode
      (numberFieldEncoding basis).encode (value ρ) :=
  Classical.choice (PlanarHom.FKTIsingMachines.fp_value basis ρ)

/-- The same value program under the original faithful codecs, with finite
alphabets on every actual stack of the refined machine. -/
def computer (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K) :
    Counting.Computation.PolyTime MixedCode.encoding.toFinEncoding
      (numberFieldEncoding basis).toFinEncoding (value ρ) :=
  Counting.Computation.FiniteSupport.toPolyTime (sourceComputer basis ρ)

theorem computer_refined (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K) :
    (computer basis ρ).toTM2ComputableInPolyTime =
      Counting.Computation.FiniteSupport.computer (sourceComputer basis ρ) := rfl

/-- Finite enumerations for all typed stack alphabets of this concrete computer. -/
@[instance_reducible] def computerAlphabet (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : K) (k : (computer basis ρ).tm.K) : Fintype ((computer basis ρ).tm.Γ k) :=
  (computer basis ρ).finiteAlphabets k

@[simp] theorem computer_time (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K) :
    (computer basis ρ).time = (sourceComputer basis ρ).time := rfl

@[simp] theorem computer_steps (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : K) (g : MixedCode) :
    ((computer basis ρ).outputsFun g).steps = ((sourceComputer basis ρ).outputsFun g).steps :=
  rfl

/-- Exact execution on the original encoded graph and field-element words. -/
def outputs (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K) (g : MixedCode) :
    TM2OutputsInTime (computer basis ρ).tm
      ((MixedCode.encoding.encode g).map (computer basis ρ).inputAlphabet.symm)
      (some (((numberFieldEncoding basis).encode (value ρ g)).map
        (computer basis ρ).outputAlphabet.symm))
      ((computer basis ρ).time.eval (MixedCode.encoding.encode g).length) :=
  (computer basis ρ).outputsFun g

@[simp] theorem outputs_steps (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : K) (g : MixedCode) :
    (outputs basis ρ g).steps = ((sourceComputer basis ρ).outputsFun g).steps := rfl

/-- Forget the symbol-support proofs while retaining all control and stack data. -/
def eraseCfg (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K) :
    (computer basis ρ).tm.Cfg → (sourceComputer basis ρ).tm.Cfg :=
  Counting.Computation.FiniteSupport.eraseComputerCfg (sourceComputer basis ρ)

/-- Every transition, including terminal `none`, commutes with erasure. -/
theorem computer_erase_step (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : K) (c : (computer basis ρ).tm.Cfg) :
    Option.map (eraseCfg basis ρ) ((computer basis ρ).tm.step c) =
      (sourceComputer basis ρ).tm.step (eraseCfg basis ρ c) :=
  Counting.Computation.FiniteSupport.computer_erase_step (sourceComputer basis ρ) c

def outputLengthPolynomial (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K) :
    Polynomial ℕ :=
  Counting.Computation.PolyTime.outputLengthPolynomial (computer basis ρ)

theorem encoded_output_length_le (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : K) (g : MixedCode) :
    ((numberFieldEncoding basis).encode (value ρ g)).length ≤
      (outputLengthPolynomial basis ρ).eval (MixedCode.encoding.encode g).length :=
  Counting.Computation.PolyTime.encoded_output_length_le (computer basis ρ) g

/-- Finite-machine membership holds on every typed graph code. -/
theorem inFP (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K) :
    Counting.Computation.InFP MixedCode.encoding.toFinEncoding
      (numberFieldEncoding basis).toFinEncoding (value ρ) :=
  ⟨computer basis ρ⟩

/-- The intermediate calibrated matching-value program also has a finite machine. -/
theorem matchingValue_inFP (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K) :
    Counting.Computation.InFP MixedCode.encoding.toFinEncoding
      (numberFieldEncoding basis).toFinEncoding (matchingValue ρ) :=
  Counting.Computation.FiniteSupport.inFP
    (PlanarHom.FKTIsingMachines.fp_matchingValue basis ρ)

/-- The computed reference sign calibrates the actual Fisher matching sum.
This statement requires no nonzero matching weight or coupling denominator. -/
theorem matchingValue_correct (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) {g : MixedCode} {bt ut : ℕ} (hg : g.PlanarValid bt ut) (ρ : K) :
    φ (matchingValue ρ g) =
      ((PlanarHom.FisherCodePipeline.code g).toMultiGraph
        (PlanarHom.FisherCodePipeline.valid hg.1)).perfectMatchingSum
          (fun e => φ ((PlanarHom.FisherCodePipeline.isingData ρ g).2.getD e.val 0)) :=
  PlanarHom.FKTIsingMachines.matchingValue_correct basis φ hg ρ

/-- Equality with the original graph partition in the original represented field. -/
theorem value_eq_partition (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) {g : MixedCode} {bt ut : ℕ}
    (hg : g.PlanarValid bt ut) (ρ : K) (hρ : 1 + φ ρ ≠ 0) :
    value ρ g = (g.toMultiGraph hg.1).partition (matrix ρ) (fun _ => 1) :=
  PlanarHom.FKTIsingMachines.value_eq_partition basis φ hg ρ hρ

/-- Runtime and planar partition semantics for the same literal value program. -/
theorem certified_value (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0) :
    Counting.Computation.InFP MixedCode.encoding.toFinEncoding
      (numberFieldEncoding basis).toFinEncoding (value ρ) ∧
    ∀ (g : MixedCode) (bt ut : ℕ) (hg : g.PlanarValid bt ut),
      value ρ g = (g.toMultiGraph hg.1).partition (matrix ρ) (fun _ => 1) :=
  ⟨inFP basis ρ, fun _ _ _ hg => value_eq_partition basis φ hg ρ hρ⟩

end Counting.Algorithm.FKT.Ising
