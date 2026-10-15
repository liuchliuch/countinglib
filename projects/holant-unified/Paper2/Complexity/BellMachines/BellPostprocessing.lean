import Paper2.Complexity.BellMachines.FieldArithmetic
import Paper2.Complexity.BellMachines.ThreeQuerySafe

/-! Actual field-coordinate postprocessors for the three-query Bell controller.
Caller context is physically erased when unused; oracle words are really parsed.
This does not claim a public isolated-root-to-coordinate conversion. -/
namespace Paper2.Complexity.BellMachines
open Computability BinaryCompose FixedFieldMachines Paper2.Algebraic
open UniversalPairReduction.ThreeQuery
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

abbrev BellInput (K ε : Type) := K × (K × (K × ε))

def firstValue (F : FixedField K n) {ε : Type} (ee : Encoding ε Bool) :
    Computes (contextEncoding F.encoding ee) F.encoding (fun p => p.1) :=
  Wiring.firstComputes F.encoding (pairEncoding F.encoding (pairEncoding F.encoding ee))

def secondValue (F : FixedField K n) {ε : Type} (ee : Encoding ε Bool) :
    Computes (contextEncoding F.encoding ee) F.encoding (fun p => p.2.1) :=
  (Wiring.secondComputes F.encoding (pairEncoding F.encoding (pairEncoding F.encoding ee))).andThen
    (Wiring.firstComputes F.encoding (pairEncoding F.encoding ee))

def thirdValue (F : FixedField K n) {ε : Type} (ee : Encoding ε Bool) :
    Computes (contextEncoding F.encoding ee) F.encoding (fun p => p.2.2.1) :=
  ((Wiring.secondComputes F.encoding (pairEncoding F.encoding (pairEncoding F.encoding ee))).andThen
    (Wiring.secondComputes F.encoding (pairEncoding F.encoding ee))).andThen
      (Wiring.firstComputes F.encoding ee)

/-- Caller query order: q14, q13, an arbitrary repeated valid query. -/
def twoYPost (F : FixedField K n) {ε : Type} (ee : Encoding ε Bool) :
    Computes (contextEncoding F.encoding ee) F.encoding (fun p => p.1 - p.2.1) :=
  subComputes F (firstValue F ee) (secondValue F ee)

/-- The same q14/q13 order and the fixed κ of the actual odd-Y witness. -/
def oneYPost (F : FixedField K n) {ε : Type} (ee : Encoding ε Bool) (κ : K) :
    Computes (contextEncoding F.encoding ee) F.encoding (fun p => -(p.1 - p.2.1) / κ) :=
  congrComputes (scaleComputes F (twoYPost F ee) (-κ⁻¹))
    (fun p => by simp only [div_eq_mul_inv, mul_neg, neg_mul])

/-- Caller query order: q13, q14, q12. -/
def twoIPost (F : FixedField K n) {ε : Type} (ee : Encoding ε Bool) :
    Computes (contextEncoding F.encoding ee) F.encoding
      (fun p => (p.1 + p.2.1 - p.2.2.1) / 2) :=
  congrComputes
    (scaleComputes F (subComputes F
      (addComputes F (firstValue F ee) (secondValue F ee)) (thirdValue F ee)) 2⁻¹)
    (fun p => by simp only [div_eq_mul_inv])

/-- Compiled two-I coordinate-answer reduction, including query validity and
answer lengths. The caller must still supply the actual graph compiler and the
true Bell value identity; no terminal conclusion is assumed by this interface. -/
def twoIReduction {α γ ε : Type} {ea : Encoding α Bool} {eq : Encoding γ Bool}
    {ee : Encoding ε Bool} (F : FixedField K n)
    {pre : α → γ × (γ × (γ × ε))} {g : γ → K}
    (A : Computes ea (contextEncoding eq ee) pre)
    (size : PolynomialOutputBound eq F.encoding g)
    (f : α → K)
    (heq : ∀ x, f x = (g (pre x).1 + g (pre x).2.1 - g (pre x).2.2.1) / 2) :
    LengthControlledOracleReduction ea F.encoding eq F.encoding f g :=
  controlledOfEq A (twoIPost F ee) size f heq

def twoYReduction {α γ ε : Type} {ea : Encoding α Bool} {eq : Encoding γ Bool}
    {ee : Encoding ε Bool} (F : FixedField K n)
    {pre : α → γ × (γ × (γ × ε))} {g : γ → K}
    (A : Computes ea (contextEncoding eq ee) pre)
    (size : PolynomialOutputBound eq F.encoding g)
    (f : α → K) (heq : ∀ x, f x = g (pre x).1 - g (pre x).2.1) :
    LengthControlledOracleReduction ea F.encoding eq F.encoding f g :=
  controlledOfEq A (twoYPost F ee) size f heq

def oneYReduction {α γ ε : Type} {ea : Encoding α Bool} {eq : Encoding γ Bool}
    {ee : Encoding ε Bool} (F : FixedField K n) (κ : K)
    {pre : α → γ × (γ × (γ × ε))} {g : γ → K}
    (A : Computes ea (contextEncoding eq ee) pre)
    (size : PolynomialOutputBound eq F.encoding g)
    (f : α → K) (heq : ∀ x, f x = -(g (pre x).1 - g (pre x).2.1) / κ) :
    LengthControlledOracleReduction ea F.encoding eq F.encoding f g :=
  controlledOfEq A (oneYPost F ee κ) size f heq

end
end Paper2.Complexity.BellMachines
