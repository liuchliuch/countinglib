import Counting.Algorithm.ProductFinitePalette.Input
import Holant.Proofs.Tractability.ProductMachine.FiniteLabels

/-!
# Same-byte frontend for the original finite-palette Product machine

The frontend codec is the original factor codec transported through the proved
occurrence/factor bijection. The runtime input is already these bytes: there is
no host-language preprocessing pass to hide from the machine cost. The original
physical parser, compiler, palette lookup, field arithmetic and output encoding
run unchanged. Arbitrary input-word rejection is not claimed.
-/

namespace Counting.Algorithm.ProductFinitePalette

open Computability Holant.Complexity Holant.Algebraic
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.LocalDrafts.Tractability

variable {K : Type} [CommSemiring K] {q : Nat}

/-- Lossless finite-label syntax codec, including the unary variable count. -/
def inputEncoding (values : Fin q → K) : Encoding (Input values) Bool where
  encode I := (ProductMachine.FiniteLabels.inputEncoding q).encode I.compile
  decode bits := ((ProductMachine.FiniteLabels.inputEncoding q).decode bits).map (restore values)
  decode_encode I := by
    simp only [Encoding.decode_encode, Option.map_some, restore_input]

@[simp] theorem inputEncoding_encode (values : Fin q → K) (I : Input values) :
    (inputEncoding values).encode I =
      (ProductMachine.FiniteLabels.inputEncoding q).encode I.compile := rfl

@[simp] theorem decode_encode_input (values : Fin q → K) (I : Input values) :
    (inputEncoding values).decode ((inputEncoding values).encode I) = some I :=
  (inputEncoding values).decode_encode I

/-- The unary variable-count prefix charges isolated variables in input bits. -/
theorem variableCount_le_inputLength (values : Fin q → K) (I : Input values) :
    I.variableCount ≤ ((inputEncoding values).encode I).length := by
  simp [inputEncoding, ProductMachine.FiniteLabels.inputEncoding,
    Holant.OneHot.StackProgram.GraphLabelEncoding.sigmaEncoding,
    GraphPreprocessing.UnaryBinary.unaryEncoding]
  omega

/-- A genuine finite identity machine also witnesses the frontend conversion.
The final solver below reuses the same bytes directly and does not need this copy. -/
noncomputable def conversionComputes (values : Fin q → K) :
    Computes (inputEncoding values) (ProductMachine.FiniteLabels.inputEncoding q)
      (Input.compile values) :=
  recode (identityComputes (ProductMachine.FiniteLabels.inputEncoding q))
    (Input.compile values) (fun _ => rfl) (fun _ => rfl)

section FixedField

variable {K : Type} [Field K] [Algebra ℚ K] {q d : Nat}
variable (F : FixedField K d) (table : Fin q → Fin d → ℚ)

/-- The field/basis and rational palette are fixed before runtime. -/
noncomputable abbrev coefficients : Fin q → K :=
  ProductMachine.FieldInterpreter.coefficients F table

/-- Exact semantic equality to the original finite-label machine specification. -/
theorem answer_eq_partition (I : Input (coefficients F table)) :
    ProductMachine.FiniteLabels.answer q F table I.compile = I.partition :=
  I.compile_partition (coefficients F table)

/-- The existing concrete solver, recoded by input-byte equality and the proved
S1 partition equation. No correctness or computer is supplied as a premise. -/
noncomputable def computes :
    Computes (inputEncoding (coefficients F table)) F.encoding
      (Input.partition (coefficients F table)) :=
  recode (ProductMachine.FiniteLabels.computes q F table)
    (Input.compile (coefficients F table)) (fun _ => rfl)
    (fun I => congrArg F.encoding.encode (answer_eq_partition F table I))

/-- The actual program is literally the original Product solver. -/
theorem same_machine :
    (computes F table).machine = (ProductMachine.FiniteLabels.computes q F table).machine := rfl

/-- Recoding keeps the original transition polynomial. -/
theorem same_time :
    (computes F table).time = (ProductMachine.FiniteLabels.computes q F table).time := rfl

noncomputable def polyTime :
    Holant.Complexity.PolyTime (inputEncoding (coefficients F table)) F.encoding
      (Input.partition (coefficients F table)) :=
  (computes F table).toPolyTime

theorem inFP :
    Holant.Complexity.InFP (inputEncoding (coefficients F table)) F.encoding
      (Input.partition (coefficients F table)) :=
  (computes F table).inFP

/-- The successful physical run starts at this public input's encoded bytes and
ends with the field encoding of this same input's S1 partition. -/
noncomputable def outputs_partition (I : Input (coefficients F table)) :
    Turing.TM2OutputsInTime (computes F table).machine.computer
      ((inputEncoding (coefficients F table)).encode I)
      (some (F.encoding.encode I.partition))
      ((computes F table).time.eval ((inputEncoding (coefficients F table)).encode I).length) :=
  (computes F table).outputs I

theorem transitions_le (I : Input (coefficients F table)) :
    ((computes F table).outputs I).steps ≤
      (computes F table).time.eval ((inputEncoding (coefficients F table)).encode I).length :=
  ((computes F table).outputs I).steps_le_m

/-- All executed primitive instructions, including parsing, scans, palette
access, exact rational arithmetic and output cleanup, belong to this same run. -/
theorem primitive_bound (I : Input (coefficients F table)) :
    primitiveCost (computes F table).machine ((computes F table).outputs I).steps
      (some (Turing.initList (computes F table).machine.computer
        ((inputEncoding (coefficients F table)).encode I))) ≤
      (primitivePolynomial (computes F table)).eval
        ((inputEncoding (coefficients F table)).encode I).length :=
  computes_primitive_cost (computes F table) I

noncomputable def answerBits (I : Input (coefficients F table)) : List Bool :=
  F.encoding.encode I.partition

theorem answerBits_decode (I : Input (coefficients F table)) :
    F.encoding.decode (answerBits F table I) = some I.partition :=
  F.encoding.decode_encode _

end FixedField
end Counting.Algorithm.ProductFinitePalette
