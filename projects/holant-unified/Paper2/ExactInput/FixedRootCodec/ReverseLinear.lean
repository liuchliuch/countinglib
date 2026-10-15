import Paper2.ExactInput.FixedRootCodec.LinearApproximation

/-! Rational point approximations for linear maps with fixed real algebraic
coefficients. This supplies the numerical part of a fixed inverse embedding
matrix: only its rational input coordinates and requested precision vary. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open scoped BigOperators
noncomputable section
variable {n : ℕ} {a : Fin n → ℝ}

def intervalMidpoint (t : ℚ × ℚ) : ℚ := (t.1+t.2)/2

def intervalMidpointComputes : Computes intervalEncoding rationalEncoding intervalMidpoint :=
  congrComputes (BellMachines.rationalProvider.mulComputes
    (BellMachines.rationalProvider.addComputes (Wiring.firstComputes rationalEncoding rationalEncoding)
      (Wiring.secondComputes rationalEncoding rationalEncoding))
    (constantComputes intervalEncoding rationalEncoding (1/2)))
    (fun t => by simp [intervalMidpoint,div_eq_mul_inv])

def realLinearMidpoint (b : ∀ i, RealBracket (a i)) (k : ℕ) (v : Fin n → ℚ) : ℚ :=
  intervalMidpoint (realLinearApproximation b k v)

def realLinearMidpointComputes (b : ∀ i, RealBracket (a i)) :
    Computes (precisionVectorEncoding n) rationalEncoding
      (fun x => realLinearMidpoint b x.1 x.2) :=
  (realLinearApproximationComputes b).andThen intervalMidpointComputes

/-- A magnitude bound is independent of the denominator precision of the
runtime rational coefficients. -/
theorem realLinearApproximation_width_abs (b : ∀ i, RealBracket (a i))
    (k : ℕ) (M : ℚ) (_hM : 0≤M) (v : Fin n → ℚ) (hv : ∀ i, |v i|≤M) :
    (realLinearApproximation b k v).2-(realLinearApproximation b k v).1≤
      (M*(∑ i, bracketWidth (b i))+2)/(2 : ℚ)^k := by
  have cell (i : Fin n) :
      (scaledInterval (v i) (realApproximation (b i) k)).2-
        (scaledInterval (v i) (realApproximation (b i) k)).1≤
      M*bracketWidth (b i)/(2 : ℚ)^k := by
    rw [scaledInterval_width]
    calc
      _≤|v i| * (bracketWidth (b i)/(2 : ℚ)^k) :=
        mul_le_mul_of_nonneg_left (realApproximation_width (b i) k) (abs_nonneg _)
      _≤M*(bracketWidth (b i)/(2 : ℚ)^k) :=
        mul_le_mul_of_nonneg_right (hv i)
          (div_nonneg (bracketWidth_nonnegative _) (by positivity))
      _=_ := by ring
  have hs := Finset.sum_le_sum (fun i (_ : i∈(Finset.univ : Finset (Fin n))) => cell i)
  rw [Finset.sum_sub_distrib,← Finset.sum_div,← Finset.mul_sum] at hs
  have he : 2*unitEpsilon k=2/(2 : ℚ)^k := by simp [unitEpsilon,div_eq_mul_inv]
  simp only [realLinearApproximation]
  calc
    _=((∑ i, (scaledInterval (v i) (realApproximation (b i) k)).2)-
      ∑ i, (scaledInterval (v i) (realApproximation (b i) k)).1)+2*unitEpsilon k := by ring
    _≤M*(∑ i, bracketWidth (b i))/(2 : ℚ)^k+2*unitEpsilon k :=
      add_le_add hs (le_refl _)
    _=_ := by rw [he]; ring

theorem realLinearMidpoint_error (b : ∀ i, RealBracket (a i)) (k : ℕ) (v : Fin n → ℚ) :
    |(realLinearMidpoint b k v : ℝ)-(∑ i, (v i : ℝ)*a i)|<
      ((realLinearApproximation b k v).2 : ℝ)-(realLinearApproximation b k v).1 := by
  have h := realLinearApproximation_contains b k v
  unfold realLinearMidpoint intervalMidpoint
  push_cast
  exact abs_lt.mpr ⟨by linarith,by linarith⟩

theorem realLinearMidpoint_error_abs (b : ∀ i, RealBracket (a i))
    (k : ℕ) (M : ℚ) (hM : 0≤M) (v : Fin n → ℚ) (hv : ∀ i, |v i|≤M) :
    |(realLinearMidpoint b k v : ℝ)-(∑ i, (v i : ℝ)*a i)|<
      ((M*(∑ i, bracketWidth (b i))+2 : ℚ) : ℝ)/(2 : ℝ)^k := by
  have hw := (Rat.cast_le (K := ℝ)).mpr (realLinearApproximation_width_abs b k M hM v hv)
  push_cast at hw
  push_cast
  exact (realLinearMidpoint_error b k v).trans_le hw

theorem realLinearMidpoint_error_magnitude_power (b : ∀ i, RealBracket (a i))
    (k H D : ℕ) (v : Fin n → ℚ) (hv : ∀ i, |v i|≤(2 : ℚ)^H)
    (hD : (∑ i, bracketWidth (b i))+2≤(2 : ℚ)^D) :
    |(realLinearMidpoint b k v : ℝ)-(∑ i, (v i : ℝ)*a i)|<
      (2 : ℝ)^(H+D)/(2 : ℝ)^k := by
  have he := realLinearMidpoint_error_abs b k ((2 : ℚ)^H) (by positivity) v hv
  push_cast at he
  have hp : (2 : ℚ)^H*(∑ i, bracketWidth (b i))+2≤(2 : ℚ)^(H+D) := by
    have hH : (1 : ℚ)≤2^H := one_le_pow₀ (by norm_num)
    calc
      _≤(2 : ℚ)^H*((∑ i, bracketWidth (b i))+2) := by nlinarith
      _≤(2 : ℚ)^H*(2 : ℚ)^D := mul_le_mul_of_nonneg_left hD (by positivity)
      _=_ := (pow_add _ _ _).symm
  have hp' := (Rat.cast_le (K := ℝ)).mpr hp
  push_cast at hp'
  exact he.trans_le (div_le_div_of_nonneg_right hp' (by positivity))

theorem realLinearMidpoint_error_power (b : ∀ i, RealBracket (a i))
    (k B D : ℕ) (v : Fin n → ℚ) (hv : ∀ i, rationalBitHeight (v i)≤B)
    (hD : (∑ i, bracketWidth (b i))+2≤(2 : ℚ)^D) :
    |(realLinearMidpoint b k v : ℝ)-(∑ i, (v i : ℝ)*a i)|<
      (2 : ℝ)^(B+D)/(2 : ℝ)^k := by
  have hw : (realLinearApproximation b k v).2-(realLinearApproximation b k v).1≤
      (2 : ℚ)^(B+D)/(2 : ℚ)^k := by
    apply (realLinearApproximation_width b k B v hv).trans
    rw [pow_add]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hD (by positivity)) (by positivity)
  have hw' := (Rat.cast_le (K := ℝ)).mpr hw
  push_cast at hw'
  exact (realLinearMidpoint_error b k v).trans_le hw'

def linearWidthExponent (b : ∀ i, RealBracket (a i)) : ℕ :=
  Classical.choose (bracketWidth_power_bound b)

theorem linearWidthExponent_bound (b : ∀ i, RealBracket (a i)) :
    (∑ i, bracketWidth (b i))+2≤(2 : ℚ)^(linearWidthExponent b) :=
  Classical.choose_spec (bracketWidth_power_bound b)

def linearPrecision (b : ∀ i, RealBracket (a i)) (s : ℕ) (v : Fin n → ℚ) : ℕ :=
  ((precisionVectorEncoding n).encode (s,v)).length+linearWidthExponent b+2

def linearPoint (b : ∀ i, RealBracket (a i)) (s : ℕ) (v : Fin n → ℚ) : ℚ :=
  realLinearMidpoint b (linearPrecision b s v) v

/-- Requested precision is a physical unary word; all extra precision needed
for variable input coefficient height is counted by the literal input scanner. -/
def linearPointComputes (b : ∀ i, RealBracket (a i)) :
    Computes (precisionVectorEncoding n) rationalEncoding (fun x => linearPoint b x.1 x.2) := by
  let counter := precisionComputes (precisionVectorEncoding n) 1 (linearWidthExponent b+2)
  let coordinates := Wiring.secondComputes UnaryBinary.unaryEncoding (vectorEncoding n)
  exact congrComputes ((pairComputes counter coordinates).andThen (realLinearMidpointComputes b))
    (fun x => by simp [linearPoint,linearPrecision,Nat.add_assoc])

theorem linearPoint_error (b : ∀ i, RealBracket (a i)) (s : ℕ) (v : Fin n → ℚ) :
    |(linearPoint b s v : ℝ)-(∑ i, (v i : ℝ)*a i)|<1/(2 : ℝ)^s := by
  let B := ((vectorEncoding n).encode v).length+1
  have he := realLinearMidpoint_error_power b (linearPrecision b s v) B
    (linearWidthExponent b) v (fun i => coordinate_height_input v i) (linearWidthExponent_bound b)
  have hk : linearPrecision b s v=B+linearWidthExponent b+(2*s+2) := by
    simp only [linearPrecision,precisionVectorEncoding,pairEncoding_length,
      UnaryBinary.unaryEncoding,List.length_replicate,B]
    omega
  have hr : (2 : ℝ)^(B+linearWidthExponent b)/(2 : ℝ)^(linearPrecision b s v)=
      1/(2 : ℝ)^(2*s+2) := by
    rw [hk]
    simp only [pow_add]
    field_simp
  have hp : (2 : ℝ)^s≤(2 : ℝ)^(2*s+2) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hi : 1/(2 : ℝ)^(2*s+2)≤1/(2 : ℝ)^s :=
    (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by simpa using hp)
  exact he.trans_le (hr.le.trans hi)

end
end Paper2.ExactInput.FixedRootCodec
