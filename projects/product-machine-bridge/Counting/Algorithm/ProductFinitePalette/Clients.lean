import Counting.Algorithm.ProductFinitePalette.Machine
import Mathlib.LinearAlgebra.Basis.Basic

/-! Independent fixed rational palette clients. All numerical equalities use
kernel reduction. Machine contracts use the actual original solver, not an
assumed evaluator for a client-indexed answer function. -/

namespace Counting.Algorithm.ProductFinitePalette.Clients

noncomputable section

open Holant.Algebraic Holant.LocalDrafts.Tractability

/-- Exact one-dimensional rational presentation with basis `(1)`. -/
noncomputable def rationalField : FixedField ℚ 1 where
  unitCode := fun _ => 1
  mulTable := fun _ _ _ => 1
  basis := Module.Basis.singleton (Fin 1) ℚ
  unit_spec := by simp [Module.Basis.equivFun_symm_apply]
  mul_spec i j := by simp [Module.Basis.equivFun_symm_apply]

@[simp] theorem rational_decode (v : Fin 1 → ℚ) : rationalField.decode v = v 0 := by
  simp [FixedField.decode, rationalField, Module.Basis.equivFun_symm_apply]

/-- Six fixed exact rational coefficients, including zero and a negative value. -/
def table : Fin 6 → Fin 1 → ℚ := fun i _ => ![0, 1, -1, 2, 3, 5] i

noncomputable abbrev values := coefficients rationalField table

@[simp] theorem values_exact (i : Fin 6) : values i = ![0, 1, -1, 2, 3, 5] i := by
  simp [values, coefficients, ProductMachine.FieldInterpreter.coefficients, table]

/-- Repeated unary occurrences, a repeated scope, and one isolated variable. -/
def repeated : Input values := ⟨3,
  [scalar values 4, unary values 0 3 5, equality values 0 1,
   unary values 1 4 3, unary values 1 4 3, equality values 1 1]⟩

theorem repeated_compile_shape :
    repeated.compile.1 = 3 ∧ repeated.compile.2.length = 6 := by decide +kernel

theorem repeated_public : repeated.toPublic =
    (⟨3, [Product.scalar 3, Product.unary 0 2 5, Product.equality 0 1,
      Product.unary 1 3 2, Product.unary 1 3 2, Product.equality 1 1]⟩ : Product.Instance ℚ) := by
  simp [repeated, Input.toPublic, publicOccurrence, scalar, unary, equality, Fin.cons, Fin.cases]
  exact ⟨rfl, rfl⟩

theorem repeated_partition : repeated.partition = 228 := by
  rw [← Input.toPublic_partition, repeated_public, ← Product.evaluate_eq_partition]
  decide +kernel

/-- Equality ties the first two variables; the third remains isolated. -/
def cancellation : Input values :=
  ⟨3, [unary values 0 1 2, equality values 0 1]⟩

theorem cancellation_partition : cancellation.partition = 0 := by
  rw [← Input.toPublic_partition, ← Product.evaluate_eq_partition]
  have h : cancellation.toPublic =
      (⟨3, [Product.unary 0 1 (-1), Product.equality 0 1]⟩ : Product.Instance ℚ) := by
    simp [cancellation, Input.toPublic, publicOccurrence, unary, equality, Fin.cons, Fin.cases]
    rfl
  rw [h]
  decide +kernel

def zeroScalar : Input values :=
  ⟨2, [scalar values 0, unary values 0 4 5]⟩

theorem zero_partition : zeroScalar.partition = 0 := by
  rw [← Input.toPublic_partition, ← Product.evaluate_eq_partition]
  have h : zeroScalar.toPublic =
      (⟨2, [Product.scalar 0, Product.unary 0 3 5]⟩ : Product.Instance ℚ) := by
    simp [zeroScalar, Input.toPublic, publicOccurrence, scalar, unary]
  rw [h]
  decide +kernel

def nullary : Input values := ⟨0, [scalar values 4, scalar values 4, scalar values 3]⟩

theorem nullary_partition : nullary.partition = 18 := by
  rw [← Input.toPublic_partition, ← Product.evaluate_eq_partition]
  have h : nullary.toPublic =
      (⟨0, [Product.scalar 3, Product.scalar 3, Product.scalar 2]⟩ : Product.Instance ℚ) := by
    simp [nullary, Input.toPublic, publicOccurrence, scalar]
  rw [h]
  decide +kernel

def isolated : Input values := ⟨5, []⟩

theorem isolated_partition : isolated.partition = 32 := by
  rw [← Input.toPublic_partition, ← Product.evaluate_eq_partition]
  change Product.evaluate (⟨5, []⟩ : Product.Instance ℚ) = 32
  decide +kernel

/-- The codec round trip preserves the occurrence structure, not just its sum. -/
theorem repeated_codec :
    (inputEncoding values).decode ((inputEncoding values).encode repeated) = some repeated :=
  decode_encode_input values repeated

/-- This client's concrete encoded input reaches the exact encoded answer in
the original finite Boolean machine with its original polynomial budget. -/
noncomputable def repeated_machine_run :
    Turing.TM2OutputsInTime (computes rationalField table).machine.computer
      ((inputEncoding values).encode repeated)
      (some (rationalField.encoding.encode 228))
      ((computes rationalField table).time.eval ((inputEncoding values).encode repeated).length) := by
  simpa only [repeated_partition] using outputs_partition rationalField table repeated

noncomputable def cancellation_machine_run :
    Turing.TM2OutputsInTime (computes rationalField table).machine.computer
      ((inputEncoding values).encode cancellation)
      (some (rationalField.encoding.encode 0))
      ((computes rationalField table).time.eval ((inputEncoding values).encode cancellation).length) := by
  simpa only [cancellation_partition] using outputs_partition rationalField table cancellation

theorem repeated_output_decode :
    rationalField.encoding.decode (answerBits rationalField table repeated) = some 228 := by
  rw [answerBits_decode, repeated_partition]

theorem cancellation_output_decode :
    rationalField.encoding.decode (answerBits rationalField table cancellation) = some 0 := by
  rw [answerBits_decode, cancellation_partition]

/-- The machine cost witness belongs to the very run used above. -/
theorem repeated_cost :
    Holant.Complexity.FixedFieldMachines.primitiveCost
      (computes rationalField table).machine ((computes rationalField table).outputs repeated).steps
      (some (Turing.initList (computes rationalField table).machine.computer
        ((inputEncoding values).encode repeated))) ≤
      (Holant.Complexity.FixedFieldMachines.primitivePolynomial (computes rationalField table)).eval
        ((inputEncoding values).encode repeated).length :=
  primitive_bound rationalField table repeated

end
end Counting.Algorithm.ProductFinitePalette.Clients
