import ComplexCSP.Algebra.ComplexRootCertificatesInput
import ComplexCSP.Algebra.EncodedNumberFieldPresentation

/-! # Literal separate algebraic-number input

An input stores only integer coefficients and a rational open isolating rectangle.
Validity is the standard semantic promise for this representation: the polynomial
is nonzero and exactly one of its complex roots lies in the rectangle. The input
polynomial is not required to be monic, irreducible, or square-free.
-/
namespace ComplexCSP.AlgebraicEncoding
open Polynomial ComplexRootCertificates
open scoped BigOperators

/-- Executable ascending-coefficient evaluation, without native polynomials. -/
def evalIntegerList {K : Type*} [Ring K] (a : List ℤ) (x : K) : K :=
  a.foldr (fun (c : ℤ) (y : K) => (c : K) + x * y) 0

/-- The integer polynomial is used only for semantics. -/
noncomputable def integerListPolynomial (a : List ℤ) : Polynomial ℤ :=
  a.foldr (fun c p => C c + X * p) 0

@[simp] theorem evalIntegerList_nil {K : Type*} [Ring K] (x : K) :
    evalIntegerList [] x = 0 := rfl
@[simp] theorem evalIntegerList_cons {K : Type*} [Ring K] (c : ℤ) (a : List ℤ) (x : K) :
    evalIntegerList (c :: a) x = (c : K) + x * evalIntegerList a x := rfl

@[simp] theorem integerListPolynomial_nil : integerListPolynomial [] = 0 := rfl
@[simp] theorem integerListPolynomial_cons (c : ℤ) (a : List ℤ) :
    integerListPolynomial (c :: a) = C c + X * integerListPolynomial a := rfl

@[simp] theorem integerListPolynomial_coeff (a : List ℤ) (k : ℕ) :
    (integerListPolynomial a).coeff k = a.getD k 0 := by
  induction a generalizing k with
  | nil => simp [integerListPolynomial]
  | cons c a ih =>
    cases k with
    | zero => simp only [integerListPolynomial_cons, coeff_add, coeff_C_zero, coeff_X_mul_zero, add_zero]; rfl
    | succ k =>
      rw [integerListPolynomial_cons, coeff_add, coeff_C, coeff_X_mul]
      simp only [Nat.add_one_ne_zero, if_false, zero_add, ih]
      rfl

@[simp] theorem integerListPolynomial_aeval {K : Type*} [CommRing K] (a : List ℤ) (x : K) :
    aeval x (integerListPolynomial a) = evalIntegerList a x := by
  induction a with
  | nil => simp
  | cons c a ih => simp [ih]

@[simp] theorem map_evalIntegerList {K R : Type*} [Ring K] [Ring R]
    (f : K →+* R) (a : List ℤ) (x : K) :
    f (evalIntegerList a x) = evalIntegerList a (f x) := by
  induction a with
  | nil => simp
  | cons c a ih => simp [ih]

/-- All literal data used to identify one exact algebraic complex number. -/
structure AlgebraicInput where
  coefficients : List ℤ
  rectangle : Rectangle
  deriving DecidableEq

/-- Exact interpretation, including uniqueness in the supplied open rectangle. -/
def AlgebraicInput.Represents (a : AlgebraicInput) (z : ℂ) : Prop :=
  integerListPolynomial a.coefficients ≠ 0 ∧
    evalIntegerList a.coefficients z = 0 ∧ a.rectangle.Contains z ∧
      ∀ w : ℂ, evalIntegerList a.coefficients w = 0 → a.rectangle.Contains w → w = z

/-- A valid finite description, with no chosen complex value as runtime data. -/
def AlgebraicInput.Valid (a : AlgebraicInput) : Prop := ∃ z, a.Represents z

 theorem AlgebraicInput.Represents.unique {a : AlgebraicInput} {z w : ℂ}
    (hz : a.Represents z) (hw : a.Represents w) : w = z := hz.2.2.2 w hw.2.1 hw.2.2.1

 theorem AlgebraicInput.Represents.isAlgebraic {a : AlgebraicInput} {z : ℂ}
    (hz : a.Represents z) : IsAlgebraic ℚ z := by
  refine ⟨(integerListPolynomial a.coefficients).map (Int.castRingHom ℚ), ?_, ?_⟩
  · exact fun h => hz.1 ((Polynomial.map_eq_zero_iff Int.cast_injective).mp h)
  · change aeval z ((integerListPolynomial a.coefficients).map (algebraMap ℤ ℚ)) = 0
    rw [aeval_map_algebraMap, integerListPolynomial_aeval]
    exact hz.2.1

 theorem integerListPolynomial_complex (a : List ℤ) :
    denote (ofIntList a) = (integerListPolynomial a).map (Int.castRingHom ℂ) :=
  denote_ofIntList_eq a _ (integerListPolynomial_coeff a)

 theorem input_root_denote {a : AlgebraicInput} {z : ℂ} (hz : a.Represents z) :
    (denote (ofIntList a.coefficients)).eval z = 0 := by
  rw [integerListPolynomial_complex, Polynomial.eval_map]
  change aeval z (integerListPolynomial a.coefficients) = 0
  rw [integerListPolynomial_aeval]
  exact hz.2.1

end ComplexCSP.AlgebraicEncoding
