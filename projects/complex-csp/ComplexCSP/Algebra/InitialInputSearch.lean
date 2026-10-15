import ComplexCSP.Algebra.InitialInputCandidateComplete
import ComplexCSP.Algebra.InitialInputCandidateSound

/-!
# Actual initial-conversion search on valid algebraic descriptions

Runtime data are finite coefficient lists and rational rectangles. The search
is total under the standard semantic validity promise, whose proof is erased.
There is no claim here that arbitrary invalid descriptions are decidable.
-/
namespace ComplexCSP.AlgebraicEncoding
open EncodedNumberField ComplexRootCertificates

/-- A cheap same-field guess for rational inputs, read solely from the first
two integer coefficients. Zero denominators and nonlinear input descriptions
are harmless: every guess still passes through the full candidate checker. -/
def rationalInitialSeed {m : ℕ} (input : Fin m → AlgebraicInput) : InitialInputCandidate m where
  degree := 1
  tail := fun _ => 0
  coordinates i _ := -((input i).coefficients.getD 0 0 : ℚ) /
    ((input i).coefficients.getD 1 0 : ℚ)
  expression := PolynomialPrograms.constant 0
  center := 0
  radius := 1

/-- A complete finite-record enumeration following the cheap rational seed. -/
def initialCandidateAt {m : ℕ} (input : Fin m → AlgebraicInput) : ℕ → InitialInputCandidate m
  | 0 => rationalInitialSeed input
  | code + 1 => (Encodable.decode (α := InitialInputCandidate m) code).getD (rationalInitialSeed input)

@[simp] theorem initialCandidateAt_encode {m : ℕ} (input : Fin m → AlgebraicInput)
    (C : InitialInputCandidate m) : initialCandidateAt input (Encodable.encode C + 1) = C := by
  simp [initialCandidateAt]

/-- Mathematical coverage of the actual natural-code enumeration. -/
theorem exists_accepted_initial_code {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) :
    ∃ code, (initialCandidateAt input code).test input = true := by
  obtain ⟨C, hC⟩ := exists_initialInputCandidate_of_valid input hinput
  exact ⟨Encodable.encode C + 1, by simpa using hC⟩

/-- Executable unbounded search, with termination proved from valid standard input. -/
def findInitialInputCode {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) : ℕ := Nat.find (exists_accepted_initial_code input hinput)

 theorem findInitialInputCode_spec {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) :
    (initialCandidateAt input (findInitialInputCode input hinput)).test input = true :=
  Nat.find_spec (exists_accepted_initial_code input hinput)

/-- The finite conversion result. No actual complex value is a runtime argument. -/
def findInitialInputCandidate {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) : InitialInputCandidate m :=
  initialCandidateAt input (findInitialInputCode input hinput)

 theorem findInitialInputCandidate_spec {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) : (findInitialInputCandidate input hinput).test input = true :=
  findInitialInputCode_spec input hinput

/-- A proof-carrying finite output; the proof is erased from executable code. -/
def searchInitialInputs {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) : {C : InitialInputCandidate m // C.test input = true} :=
  ⟨findInitialInputCandidate input hinput, findInitialInputCandidate_spec input hinput⟩

/-- If the finite seed passes, the actual search returns it immediately. -/
theorem findInitialInputCode_eq_zero_of_seed {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) (hseed : (rationalInitialSeed input).test input = true) :
    findInitialInputCode input hinput = 0 := by
  apply Nat.le_zero.mp
  exact Nat.find_min' (exists_accepted_initial_code input hinput) hseed

 theorem findInitialInputCandidate_eq_seed {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) (hseed : (rationalInitialSeed input).test input = true) :
    findInitialInputCandidate input hinput = rationalInitialSeed input := by
  rw [findInitialInputCandidate, findInitialInputCode_eq_zero_of_seed input hinput hseed]
  rfl

/-- The searched finite result realizes exactly the originally represented
complex values. The embedding occurs solely in the correctness theorem. -/
theorem findInitialInputCandidate_sound {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) (z : Fin m → ℂ)
    (hz : ∀ i, (input i).Represents (z i)) :
    let C := findInitialInputCandidate input hinput
    letI : Fact (Element.Valid C.degree (EffectiveRoots.coefficientRelation C.tail)) :=
      ⟨validTail_sound C.tail (InitialInputCandidate.test_valid
        (findInitialInputCandidate_spec input hinput))⟩
    ∃ σ : C.FieldType →+* ℂ,
      (∀ i, σ (C.coordinateValue i) = z i) ∧
      PolynomialPrograms.interpret (algebraMap ℚ ℂ) z C.expression = σ Element.generator :=
  (findInitialInputCandidate input hinput).sound input z hz (findInitialInputCandidate_spec input hinput)

end ComplexCSP.AlgebraicEncoding
