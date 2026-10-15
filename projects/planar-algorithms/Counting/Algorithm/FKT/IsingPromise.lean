import Counting.Algorithm.FKT.Ising
import PlanarHom.FKTIsingTractability

/-!
# Ordinary raw-input Ising on finite-stack machines

The input is the original raw bit word together with a proof-only planar promise.
Its codec adds no tags, framing, drawing, or planarity certificate. The source
witness is chosen from the original `ising_inFP` theorem, whose machine already
normalizes successful noncanonical encodings. Its output is already an encoded
field element, so the external output codec is the identity on bit words.

Finite-support refinement preserves this raw witness's time and exact steps.
The clock is evaluated at the literal raw-word length. Raw-code normalization
is already part of this witness; the typed evaluator has a separate witness.
-/

noncomputable section

namespace Counting.Algorithm.FKT.IsingPromise

open Turing PlanarHom.Complexity

/-- All successful ordinary encodings of planar one-label graphs with no unaries. -/
abbrev RawInput := {raw : Bits // MixedCode.PlanarInput 1 0 raw}

/-- The original word is encoded literally; the promise proof occupies no tape. -/
def inputCode : BitEncoding RawInput :=
  BitEncoding.bits.restrict (MixedCode.PlanarInput 1 0)

@[simp] theorem inputCode_encode (x : RawInput) : inputCode.encode x = x.val := rfl

variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}

/-- The original homogeneous zero-field evaluation problem. -/
def problem (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K) : PromiseProblem :=
  MixedCode.evaluationProblem basis (fun _ : Fin 1 => Ising.matrix ρ)
    (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1)

@[simp] theorem problem_valid (basis : Module.Basis (Fin dimension) ℚ K)
    (ρ : K) (raw : Bits) :
    (problem basis ρ).valid raw = MixedCode.PlanarInput 1 0 raw := rfl

/-- The promise target already returns encoded field-element bits. -/
def rawValue (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K) (x : RawInput) : Bits :=
  (problem basis ρ).value x.val

/-- Fix the actual witness of the original raw promised theorem, including its
proved normalizer for successful noncanonical input encodings. -/
def sourceComputer (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0) :
    TM2ComputableInPolyTime inputCode.encode BitEncoding.bits.encode (rawValue basis ρ) :=
  Classical.choice (PlanarHom.FKTIsingMachines.ising_inFP basis φ ρ hρ)

/-- The source is exactly the original theorem's selected computer. -/
theorem sourceComputer_eq_original (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0) :
    sourceComputer basis φ ρ hρ =
      (PlanarHom.FKTIsingMachines.ising_inFP basis φ ρ hρ).computer := rfl

/-- A finite alphabet on every stack, with the same literal raw input/output words. -/
def computer (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0) :
    Counting.Computation.PolyTime inputCode.toFinEncoding BitEncoding.bits.toFinEncoding
      (rawValue basis ρ) :=
  Counting.Computation.FiniteSupport.toPolyTime (sourceComputer basis φ ρ hρ)

theorem computer_refined (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0) :
    (computer basis φ ρ hρ).toTM2ComputableInPolyTime =
      Counting.Computation.FiniteSupport.computer (sourceComputer basis φ ρ hρ) := rfl

@[instance_reducible] def computerAlphabet (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0)
    (k : (computer basis φ ρ hρ).tm.K) : Fintype ((computer basis φ ρ hρ).tm.Γ k) :=
  (computer basis φ ρ hρ).finiteAlphabets k

@[simp] theorem computer_time (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0) :
    (computer basis φ ρ hρ).time = (sourceComputer basis φ ρ hρ).time := rfl

@[simp] theorem computer_steps (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0) (x : RawInput) :
    ((computer basis φ ρ hρ).outputsFun x).steps =
      ((sourceComputer basis φ ρ hρ).outputsFun x).steps := rfl

/-- Execution is charged against the literal input word, with no second encoding. -/
def outputs (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0)
    (raw : Bits) (valid : MixedCode.PlanarInput 1 0 raw) :
    TM2OutputsInTime (computer basis φ ρ hρ).tm
      (raw.map (computer basis φ ρ hρ).inputAlphabet.symm)
      (some (((problem basis ρ).value raw).map (computer basis φ ρ hρ).outputAlphabet.symm))
      ((computer basis φ ρ hρ).time.eval raw.length) where
  steps := ((computer basis φ ρ hρ).outputsFun ⟨raw, valid⟩).steps
  steps_le_m := by
    simpa only [BitEncoding.toFinEncoding, inputCode, BitEncoding.restrict,
      BitEncoding.bits, id_eq] using
      ((computer basis φ ρ hρ).outputsFun ⟨raw, valid⟩).steps_le_m
  evals_in_steps := by
    simpa only [Equiv.invFun_as_coe, BitEncoding.toFinEncoding, inputCode,
      BitEncoding.restrict, BitEncoding.bits, rawValue, id_eq] using
      ((computer basis φ ρ hρ).outputsFun ⟨raw, valid⟩).evals_in_steps

@[simp] theorem outputs_steps (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0)
    (raw : Bits) (valid : MixedCode.PlanarInput 1 0 raw) :
    (outputs basis φ ρ hρ raw valid).steps =
      ((sourceComputer basis φ ρ hρ).outputsFun ⟨raw, valid⟩).steps := rfl

def eraseCfg (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0) :
    (computer basis φ ρ hρ).tm.Cfg → (sourceComputer basis φ ρ hρ).tm.Cfg :=
  Counting.Computation.FiniteSupport.eraseComputerCfg (sourceComputer basis φ ρ hρ)

/-- Step erasure preserves the actual raw-input program, including termination. -/
theorem computer_erase_step (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0)
    (c : (computer basis φ ρ hρ).tm.Cfg) :
    Option.map (eraseCfg basis φ ρ hρ) ((computer basis φ ρ hρ).tm.step c) =
      (sourceComputer basis φ ρ hρ).tm.step (eraseCfg basis φ ρ hρ c) :=
  Counting.Computation.FiniteSupport.computer_erase_step (sourceComputer basis φ ρ hρ) c

def outputLengthPolynomial (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0) : Polynomial ℕ :=
  Counting.Computation.PolyTime.outputLengthPolynomial (computer basis φ ρ hρ)

/-- The materialized answer length is polynomial in the unchanged raw word length. -/
theorem encoded_output_length_le (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0)
    (raw : Bits) (valid : MixedCode.PlanarInput 1 0 raw) :
    ((problem basis ρ).value raw).length ≤
      (outputLengthPolynomial basis φ ρ hρ).eval raw.length := by
  change ((problem basis ρ).value raw).length ≤
    (Counting.Computation.PolyTime.outputLengthPolynomial (computer basis φ ρ hρ)).eval raw.length
  simpa only [BitEncoding.toFinEncoding, inputCode, BitEncoding.restrict,
    BitEncoding.bits, rawValue, id_eq] using
    Counting.Computation.PolyTime.encoded_output_length_le
      (computer basis φ ρ hρ) ⟨raw, valid⟩

/-- F1 membership for the complete original ordinary planar raw-input promise. -/
theorem inFP (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0) :
    Counting.Computation.InFP inputCode.toFinEncoding BitEncoding.bits.toFinEncoding
      (rawValue basis ρ) :=
  ⟨computer basis φ ρ hρ⟩

/-- Successful decoding plus the original planar promise gives an admissible word. -/
theorem valid_of_decode {raw : Bits} {g : MixedCode}
    (hd : MixedCode.encoding.decode raw = some g) (hg : g.PlanarValid 1 0) :
    MixedCode.PlanarInput 1 0 raw :=
  ⟨g, hd, hg⟩

/-- The promise target is the exact encoded partition of any successfully decoded
graph. This target equation itself has no coupling or real-embedding premise. -/
theorem value_decode (basis : Module.Basis (Fin dimension) ℚ K) (ρ : K)
    (raw : Bits) (g : MixedCode) (hd : MixedCode.encoding.decode raw = some g)
    (hg : g.PlanarValid 1 0) :
    (problem basis ρ).value raw =
      (numberFieldEncoding basis).encode
        ((g.toMultiGraph hg.1).partition (Ising.matrix ρ) (fun _ => 1)) := by
  change MixedCode.evaluationValue basis (fun _ : Fin 1 => Ising.matrix ρ)
    (fun u : Fin 0 => Fin.elim0 u) (fun _ => 1) raw = _
  rw [MixedCode.evaluationValue_decode basis _ _ _ raw g hd hg.1]
  exact congrArg (numberFieldEncoding basis).encode
    (MixedCode.evaluate_homogeneous g hg.1 (Ising.matrix ρ) (fun _ => 1))

/-- The same successful raw word targets the typed numeric program's answer. -/
theorem value_decode_eq_value (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0)
    (raw : Bits) (g : MixedCode) (hd : MixedCode.encoding.decode raw = some g)
    (hg : g.PlanarValid 1 0) :
    (problem basis ρ).value raw = (numberFieldEncoding basis).encode (Ising.value ρ g) := by
  rw [value_decode basis ρ raw g hd hg, Ising.value_eq_partition basis φ hg ρ hρ]

/-- Full execution-to-decoded-partition contract on every successful raw encoding.
No drawing, rotation, matching, or canonical-word hypothesis is added. -/
def outputs_decode (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0)
    (raw : Bits) (g : MixedCode) (hd : MixedCode.encoding.decode raw = some g)
    (hg : g.PlanarValid 1 0) :
    TM2OutputsInTime (computer basis φ ρ hρ).tm
      (raw.map (computer basis φ ρ hρ).inputAlphabet.symm)
      (some (((numberFieldEncoding basis).encode
        ((g.toMultiGraph hg.1).partition (Ising.matrix ρ) (fun _ => 1))).map
          (computer basis φ ρ hρ).outputAlphabet.symm))
      ((computer basis φ ρ hρ).time.eval raw.length) where
  steps := (outputs basis φ ρ hρ raw (valid_of_decode hd hg)).steps
  steps_le_m := (outputs basis φ ρ hρ raw (valid_of_decode hd hg)).steps_le_m
  evals_in_steps := by
    simpa only [value_decode basis ρ raw g hd hg] using
      (outputs basis φ ρ hρ raw (valid_of_decode hd hg)).evals_in_steps

@[simp] theorem outputs_decode_steps (basis : Module.Basis (Fin dimension) ℚ K)
    (φ : K →+* ℝ) (ρ : K) (hρ : 1 + φ ρ ≠ 0)
    (raw : Bits) (g : MixedCode) (hd : MixedCode.encoding.decode raw = some g)
    (hg : g.PlanarValid 1 0) :
    (outputs_decode basis φ ρ hρ raw g hd hg).steps =
      ((sourceComputer basis φ ρ hρ).outputsFun ⟨raw, valid_of_decode hd hg⟩).steps := rfl

end Counting.Algorithm.FKT.IsingPromise
