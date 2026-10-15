import Holant.Complexity.BinaryCompose.Interface
import Holant.Algebraic.FixedFamilySize
import Paper2.FixedFieldOutput.LinearMachines

/-! Operational reuse of a proved Paper 1 Boolean-stack evaluator. The finite
program, initial state, tapes, clock and transition trace are retained literally.
Its fixed number-field answers are then converted by an actual fixed rational
linear-map program to the canonical Paper 2 coefficient-field coordinates.
No isolated-root output converter is asserted by this module. -/
namespace Paper2.TractableAlgorithms.Paper1Machine
open Computability Paper2.Complexity Paper2.Complexity.BinaryCompose FixedFieldMachines
open Paper2.ExactInput Paper2.Problem Paper2.Tractable Paper2.FixedFieldOutput
noncomputable section

/-- The Paper 1 program is already a finite Boolean-stack program. Copying its
bundle changes no instruction or finite alphabet. -/
def machine (m : Holant.Complexity.BinaryCompose.Machine) : Machine where
  K := m.K
  decidableK := m.decidableK
  finiteK := m.finiteK
  input := m.input
  output := m.output
  Label := m.Label
  finiteLabel := m.finiteLabel
  main := m.main
  State := m.State
  finiteState := m.finiteState
  initial := m.initial
  program := m.program

@[simp] theorem machine_computer (m : Holant.Complexity.BinaryCompose.Machine) :
    (machine m).computer = m.computer := rfl

/-- This operational receipt is the original receipt, including its exact
transition count. There is no normal-form compilation assumption. -/
def computes {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (m : Holant.Complexity.BinaryCompose.Computes ea eb f) :
    Computes ea eb f where
  machine := machine m.machine
  time := m.time
  outputs := m.outputs

@[simp] theorem computes_time {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (m : Holant.Complexity.BinaryCompose.Computes ea eb f) :
    (computes m).time = m.time := rfl

@[simp] theorem computes_program {A B : Type} {ea : Encoding A Bool}
    {eb : Encoding B Bool} {f : A → B}
    (m : Holant.Complexity.BinaryCompose.Computes ea eb f) :
    (computes m).machine.program = m.machine.program := rfl

/-- Only finitely many rational entries of this fixed map become constants in
the conversion program. The projection is used to select them before input. -/
def coordinates {n : ℕ} (L : Language)
    (decode : (Fin n → ℚ) →ₗ[ℚ] AlgebraicComplex) :
    (Fin n → ℚ) →ₗ[ℚ] Answer L :=
  L.fieldPresentation.basis.equivFun.toLinearMap.comp
    ((projection L).comp decode)

def coordinatesComputes {n : ℕ} (L : Language)
    (decode : (Fin n → ℚ) →ₗ[ℚ] AlgebraicComplex) :
    Computes (Paper2.Algebraic.vectorEncoding n) (answerEncoding L)
      (coordinates L decode) := linearComputes (coordinates L decode)

theorem coordinates_correct {n : ℕ} (L : Language)
    (decode : (Fin n → ℚ) →ₗ[ℚ] AlgebraicComplex) (v : Fin n → ℚ)
    (w : Wiring) (G : Instance L) (h : decode v = value w L G) :
    coordinates L decode v = answer w L G := by
  change L.fieldPresentation.basis.equivFun (projection L (decode v)) = _
  rw [h, ← answer_correct w L G, projection_embed]
  exact L.fieldPresentation.basis.equivFun.apply_symm_apply _

/-- Plug any already proved evaluator into the literal Paper 2 input/output
contract. The hypotheses are equalities of graph bytes and actual values; the
new computation executes the reused evaluator and the rational converter. -/
def evaluation {A : Type} {n : ℕ} (L : Language) (w : Wiring)
    (ea : Encoding A Bool) (f : A → Fin n → ℚ)
    (decode : (Fin n → ℚ) →ₗ[ℚ] AlgebraicComplex)
    (m : Holant.Complexity.BinaryCompose.Computes ea
      (Paper2.Algebraic.vectorEncoding n) f)
    (input : Instance L → A)
    (bytes : ∀ G, ea.encode (input G) = (inputEncoding L).encode G)
    (correct : ∀ G, decode (f (input G)) = value w L G) :
    Computes (inputEncoding L) (answerEncoding L) (answer w L) :=
  congrComputes
    ((recode (computes m) input bytes (fun _ => rfl)).andThen
      (coordinatesComputes L decode))
    (fun G => coordinates_correct L decode _ w G (correct G))

theorem booleanFP {A : Type} {n : ℕ} (L : Language) (w : Wiring)
    (ea : Encoding A Bool) (f : A → Fin n → ℚ)
    (decode : (Fin n → ℚ) →ₗ[ℚ] AlgebraicComplex)
    (m : Holant.Complexity.BinaryCompose.Computes ea
      (Paper2.Algebraic.vectorEncoding n) f)
    (input : Instance L → A)
    (bytes : ∀ G, ea.encode (input G) = (inputEncoding L).encode G)
    (correct : ∀ G, decode (f (input G)) = value w L G) :
    BooleanFP w L := ⟨evaluation L w ea f decode m input bytes correct⟩

@[simp] theorem frame_eq (bits : List Bool) :
    Holant.Algebraic.frame bits = Paper2.Algebraic.frame bits := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp only [Holant.Algebraic.frame, Paper2.Algebraic.frame, ih]

@[simp] theorem rational_bytes_eq (q : ℚ) :
    Holant.Algebraic.rationalEncoding.encode q = Paper2.Algebraic.rationalEncoding.encode q := rfl

@[simp] theorem vector_bytes_eq (n : ℕ) (v : Fin n → ℚ) :
    (Holant.Algebraic.vectorEncoding n).encode v =
      (Paper2.Algebraic.vectorEncoding n).encode v := by
  change Holant.Algebraic.vectorEncode n v = Paper2.Algebraic.vectorEncode n v
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Holant.Algebraic.vectorEncode, Paper2.Algebraic.vectorEncode,
      rational_bytes_eq, frame_eq, ih]

/-- Reinterpret the actual Paper 1 field answer as its rational coordinates.
The bytes coincide; even the coordinate extraction costs no new transition. -/
def fieldCoordinates {A K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (ea : Encoding A Bool) (F : Holant.Algebraic.FixedField K n) (f : A → K)
    (m : Holant.Complexity.BinaryCompose.Computes ea F.encoding f) :
    Computes ea (Paper2.Algebraic.vectorEncoding n) (fun a => F.decode.symm (f a)) :=
  recode (computes m) id (fun _ => rfl)
    (fun a => vector_bytes_eq n (F.decode.symm (f a)))

/-- The complete actual program for a field-valued Paper 1 evaluator. The sole
postprocessing is a fixed rational linear map, charged by its compiled clock. -/
def fieldEvaluation {A K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (L : Language) (w : Wiring) (ea : Encoding A Bool)
    (F : Holant.Algebraic.FixedField K n) (f : A → K)
    (embed : K →ₗ[ℚ] AlgebraicComplex)
    (m : Holant.Complexity.BinaryCompose.Computes ea F.encoding f)
    (input : Instance L → A)
    (bytes : ∀ G, ea.encode (input G) = (inputEncoding L).encode G)
    (correct : ∀ G, embed (f (input G)) = value w L G) :
    Computes (inputEncoding L) (answerEncoding L) (answer w L) := by
  let imported := recode (fieldCoordinates ea F f m) input bytes (fun _ => rfl)
  let decode := embed.comp F.decode.toLinearMap
  apply congrComputes (imported.andThen (coordinatesComputes L decode))
  intro G
  apply coordinates_correct L decode _ w G
  simpa [decode] using correct G

theorem fieldBooleanFP {A K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (L : Language) (w : Wiring) (ea : Encoding A Bool)
    (F : Holant.Algebraic.FixedField K n) (f : A → K)
    (embed : K →ₗ[ℚ] AlgebraicComplex)
    (m : Holant.Complexity.BinaryCompose.Computes ea F.encoding f)
    (input : Instance L → A)
    (bytes : ∀ G, ea.encode (input G) = (inputEncoding L).encode G)
    (correct : ∀ G, embed (f (input G)) = value w L G) :
    BooleanFP w L := ⟨fieldEvaluation L w ea F f embed m input bytes correct⟩

/-- A fixed rational map into the original evaluator's basis. Only the images
of finitely many target basis vectors are stored in the compiled program. -/
def reverseCoordinates {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (L : Language) (F : Holant.Algebraic.FixedField K n)
    (embed : K →ₗ[ℚ] AlgebraicComplex) : Answer L →ₗ[ℚ] (Fin n → ℚ) :=
  F.basis.equivFun.toLinearMap.comp
    (embed.leftInverse.comp (L.coefficientField.val.toLinearMap.comp
      L.fieldPresentation.decode.toLinearMap))

def reverseCoordinatesComputes {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (L : Language) (F : Holant.Algebraic.FixedField K n)
    (embed : K →ₗ[ℚ] AlgebraicComplex) :
    Computes (answerEncoding L) (Paper2.Algebraic.vectorEncoding n)
      (reverseCoordinates L F embed) := linearComputes (reverseCoordinates L F embed)

theorem leftInverse_embed {K : Type} [Field K] [Algebra ℚ K]
    (embed : K →ₗ[ℚ] AlgebraicComplex) (injective : Function.Injective embed) (x : K) :
    embed.leftInverse (embed x) = x := by
  apply LinearMap.leftInverse_apply_of_inj
  exact LinearMap.ker_eq_bot.mpr injective

/-- No assertion is made that arbitrary field coordinates belong to the old
field. Correctness concerns the equal actual graph value, exactly as needed by
an oracle reduction. -/
theorem reverseCoordinates_correct {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (L : Language) (F : Holant.Algebraic.FixedField K n)
    (embed : K →ₗ[ℚ] AlgebraicComplex) (injective : Function.Injective embed)
    (w : Wiring) (G : Instance L) (x : K) (h : embed x = value w L G) :
    reverseCoordinates L F embed (answer w L G) = F.decode.symm x := by
  change F.basis.equivFun
    (embed.leftInverse (L.fieldPresentation.decode (answer w L G) : AlgebraicComplex)) = _
  rw [answer_correct w L G, ← h, leftInverse_embed embed injective]
  rfl

/-- The reverse converter emits exactly the original field encoding, using a
proved rational-matrix program and byte-identical basis reinterpretation. -/
def fieldConversionBack {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (L : Language) (F : Holant.Algebraic.FixedField K n)
    (embed : K →ₗ[ℚ] AlgebraicComplex) :
    Computes (answerEncoding L) F.encoding
      (fun v => F.decode (reverseCoordinates L F embed v)) :=
  recode (reverseCoordinatesComputes L F embed) id (fun _ => rfl)
    (fun v => (vector_bytes_eq n (reverseCoordinates L F embed v)).symm.trans
      (Holant.Algebraic.FixedField.encoding_decode F _).symm)

theorem fieldConversionBack_correct {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}
    (L : Language) (F : Holant.Algebraic.FixedField K n)
    (embed : K →ₗ[ℚ] AlgebraicComplex) (injective : Function.Injective embed)
    (w : Wiring) (G : Instance L) (x : K) (h : embed x = value w L G) :
    F.decode (reverseCoordinates L F embed (answer w L G)) = x := by
  rw [reverseCoordinates_correct L F embed injective w G x h]
  exact F.decode.apply_symm_apply x

end
end Paper2.TractableAlgorithms.Paper1Machine
