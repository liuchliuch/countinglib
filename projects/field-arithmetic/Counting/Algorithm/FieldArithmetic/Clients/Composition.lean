import Counting.Algorithm.FieldArithmetic

/-! An independent client computes a normalized difference and checks its exact
target value. All four inputs are runtime encoded values in one fixed basis. -/
namespace Counting.Algorithm.FieldArithmetic.Clients.Composition
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines Turing
noncomputable section
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

abbrev Input (K : Type) := (K × K) × (K × K)

def inputEncoding : BitEncoding (Input K) :=
  let e := numberFieldEncoding basis
  (e.prod e).prod (e.prod e)

def outputEncoding : BitEncoding (K × Bool) :=
  (numberFieldEncoding basis).prod BitEncoding.bool

def normalizeAndCompare (p : Input K) : K × Bool :=
  let q := (p.1.1 - p.1.2) / p.2.1
  (q, decide (q = p.2.2))

theorem fp_normalizeAndCompare : FP (inputEncoding basis) (outputEncoding basis)
    (normalizeAndCompare : Input K → K × Bool) := by
  let e := numberFieldEncoding basis
  have hl := fp_fst (e.prod e) (e.prod e)
  have hr := fp_snd (e.prod e) (e.prod e)
  have hs := hl.comp (FieldArithmetic.fp_subtraction basis)
  have hd := hr.comp (fp_fst e e)
  have ht := hr.comp (fp_snd e e)
  have hq := (hs.pair hd).comp (FieldArithmetic.fp_division basis)
  have he := (hq.pair ht).comp (FieldArithmetic.fp_equality basis)
  exact hq.pair he

def computer : TM2ComputableInPolyTime (inputEncoding basis).encode
    (outputEncoding basis).encode (normalizeAndCompare : Input K → K × Bool) :=
  Classical.choice (fp_normalizeAndCompare basis)

def outputs (p : Input K) : TM2OutputsInTime (computer basis).tm
    (((inputEncoding basis).encode p).map (computer basis).inputAlphabet.symm)
    (some (((outputEncoding basis).encode (normalizeAndCompare p)).map
      (computer basis).outputAlphabet.symm))
    ((computer basis).time.eval ((inputEncoding basis).encode p).length) :=
  (computer basis).outputsFun p

theorem steps_bound (p : Input K) : (outputs basis p).steps ≤
    (computer basis).time.eval ((inputEncoding basis).encode p).length :=
  (outputs basis p).steps_le_m

def outputLengthPolynomial : Polynomial ℕ := MachineComposition.outputLengthPolynomial (computer basis)

theorem output_length_bound (p : Input K) :
    ((outputEncoding basis).encode (normalizeAndCompare p)).length ≤
      (outputLengthPolynomial basis).eval ((inputEncoding basis).encode p).length :=
  MachineComposition.encoded_output_length_le (computer basis) p

omit [Algebra ℚ K] in
theorem check_correct (p : Input K) :
    (normalizeAndCompare p).2 = true ↔ (p.1.1 - p.1.2) / p.2.1 = p.2.2 := by
  simp [normalizeAndCompare]

omit [Algebra ℚ K] in
/-- With a nonzero divisor the test verifies the corresponding affine equation.
This hypothesis is needed only for this semantic interpretation, not for FP. -/
theorem check_affine_equation (p : Input K) (hz : p.2.1 ≠ 0) :
    (normalizeAndCompare p).2 = true ↔ p.1.1 - p.1.2 = p.2.2 * p.2.1 := by
  rw [check_correct, div_eq_iff hz]

omit [Algebra ℚ K] in
theorem division_zero (x y target : K) :
    normalizeAndCompare ((x, y), (0, target)) = (0, decide ((0 : K) = target)) := by
  simp [normalizeAndCompare]

def rationalBasis : Module.Basis (Fin 1) ℚ ℚ := Module.Basis.singleton (Fin 1) ℚ

theorem rational_value : normalizeAndCompare (((7, 3), (2, 2)) : Input ℚ) = (2, true) := by
  norm_num [normalizeAndCompare]

def rational_outputs : TM2OutputsInTime (computer rationalBasis).tm
    (((inputEncoding rationalBasis).encode ((7, 3), (2, 2))).map
      (computer rationalBasis).inputAlphabet.symm)
    (some (((outputEncoding rationalBasis).encode (2, true)).map
      (computer rationalBasis).outputAlphabet.symm))
    ((computer rationalBasis).time.eval
      ((inputEncoding rationalBasis).encode ((7, 3), (2, 2))).length) := by
  simpa only [rational_value] using outputs rationalBasis ((7, 3), (2, 2))

theorem zero_divisor_accepts_zero :
    normalizeAndCompare (((7, 3), (0, 0)) : Input ℚ) = (0, true) := by
  norm_num [normalizeAndCompare]

theorem zero_divisor_rejects_one :
    normalizeAndCompare (((7, 3), (0, 1)) : Input ℚ) = (0, false) := by
  norm_num [normalizeAndCompare]

def zero_divisor_outputs : TM2OutputsInTime (computer rationalBasis).tm
    (((inputEncoding rationalBasis).encode ((7, 3), (0, 1))).map
      (computer rationalBasis).inputAlphabet.symm)
    (some (((outputEncoding rationalBasis).encode (0, false)).map
      (computer rationalBasis).outputAlphabet.symm))
    ((computer rationalBasis).time.eval
      ((inputEncoding rationalBasis).encode ((7, 3), (0, 1))).length) := by
  simpa only [zero_divisor_rejects_one] using outputs rationalBasis ((7, 3), (0, 1))

end
end Counting.Algorithm.FieldArithmetic.Clients.Composition
