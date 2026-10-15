import Counting.Reduction.FixedGadget.Extension
import Counting.Reduction.FixedGadget.S1
import Holant.Complexity.FixedGadgetSubstitution.Identity

/-! Independent use of the public compiler: two copies of a nontrivial binary
macro, each with its own internal equality edge. Equality is an explicit fixed
kernel in this client, not a resource granted by the public interface. -/
namespace Counting.Reduction.FixedGadget.Client
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open RawClosedNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

abbrev arity (_ : ℕ) : ℕ := 2

def binaryMacro : Template where
  boundary := 2
  vertices := [(0, [.inl 0, .inr (0, false)]), (0, [.inr (0, true), .inl 1])]
  edges := [0]

theorem binaryMacro_valid : binaryMacro.WellFormed 1 1 arity := by decide

def templates (i : ℕ) : Template :=
  if i = 0 then identityTemplate arity 0 else binaryMacro

theorem templates_valid : ∀ i < 2, (templates i).WellFormed 1 1 arity := by
  intro i _
  by_cases hi : i = 0
  · simpa [templates, hi] using (identityTemplate_wellFormed (b := 1) arity (0 : Fin 1))
  · simpa [templates, hi] using binaryMacro_valid

theorem boundaries : sourceArity templates = arity := by
  funext i
  by_cases hi : i = 0 <;> simp [sourceArity, templates, hi, identityTemplate, binaryMacro, arity]

def base (i : Fin 1) : Signature ℕ (arity i.val) :=
  fun x => if x 0 then (if x 1 then 4 else 3) else (if x 1 then 2 else 1)

def kernels (_ : Fin 1) (a b : Bool) : ℕ := if a = b then 1 else 0

/-- The macro really multiplies the matrix [[1,2],[3,4]] by itself. -/
def extension (i : Fin 2) : Signature ℕ (sourceArity templates i.val) :=
  fun x => if i.val = 0 then
    (if x ⟨0, by rw [boundaries]; exact Nat.zero_lt_succ _⟩ then
      (if x ⟨1, by rw [boundaries]; exact Nat.lt_succ_self _⟩ then 4 else 3)
      else (if x ⟨1, by rw [boundaries]; exact Nat.lt_succ_self _⟩ then 2 else 1))
  else
    (if x ⟨0, by rw [boundaries]; exact Nat.zero_lt_succ _⟩ then
      (if x ⟨1, by rw [boundaries]; exact Nat.lt_succ_self _⟩ then 22 else 15)
      else (if x ⟨1, by rw [boundaries]; exact Nat.lt_succ_self _⟩ then 10 else 7))

theorem local_exact : ∀ i : Fin 2,
    macroSignatures templates templates_valid base kernels i = extension i := by
  decide

/-- The same additional label occurs twice; external ends retain their order. -/
def repeatedRaw : RawClosedNetwork where
  vertices := [(1, [(0, false), (1, false)]), (1, [(0, true), (1, true)])]
  edges := [0, 0]

theorem repeated_valid : repeatedRaw.WellFormed 2 1 (sourceArity templates) := by
  decide

def repeated : Input 2 1 (sourceArity templates) := ⟨repeatedRaw, repeated_valid⟩

def output : Input 1 1 arity := compile templates templates_valid repeated

/-- The actual record list exposes two independent fresh internal edges, 2 and 3. -/
theorem output_records : output.val =
    ⟨[(0, [(0, false), (2, false)]), (0, [(2, true), (1, false)]),
      (0, [(0, true), (3, false)]), (0, [(3, true), (1, true)])], [0, 0, 0, 0]⟩ := by
  rfl

theorem independent_internal_copies :
    (output.val.vertices[0]!).2[1]! = (2, false) ∧
    (output.val.vertices[2]!).2[1]! = (3, false) ∧ (2 : ℕ) ≠ 3 := by decide

/-- Codec -> actual compiler -> faithful output decoding. -/
theorem output_codec_roundtrip :
    (validatedEncoding 1 1 arity).decode
      ((validatedEncoding 1 1 arity).encode (compile templates templates_valid repeated)) =
      some output :=
  (validatedEncoding 1 1 arity).decode_encode output

theorem source_value : value extension kernels repeated = 858 := by decide

/-- The expanded value follows from substitution correctness, not output enumeration. -/
theorem output_value : value base kernels output = 858 := by
  rw [show output = compile templates templates_valid repeated from rfl]
  rw [value_compile templates templates_valid extension base kernels local_exact, source_value]

/-- This client's concrete finite machine is obtained through the public endpoint. -/
def countReduction := parsimonious templates templates_valid extension base kernels local_exact

theorem output_encoded_bound :
    ((validatedEncoding 1 1 arity).encode output).length ≤
      (querySizePolynomial 1 1 2 2 1).eval
        ((validatedEncoding 2 1 (sourceArity templates)).encode repeated).length := by
  apply output_length_static templates templates_valid 2 2 1
  · intro i hi; rfl
  · intro i hi
    have h : i = 0 ∨ i = 1 := by omega
    rcases h with rfl | rfl <;> decide

/-- The same source and actual output agree after the public S1 network adapter. -/
theorem s1_output_value :
    (Bridge.Holant.toOpenInstance (output.val.realize output.property base kernels)).partition
      Fin.elim0 = 858 := by
  rw [Bridge.Holant.partition_toOpenInstance]
  exact output_value

/-- Empty graph input is supported without inventing isolated S1 variables. -/
def empty : Input 2 1 (sourceArity templates) := ⟨⟨[], []⟩, by decide⟩

theorem empty_output : (compile templates templates_valid empty).val = ⟨[], []⟩ := rfl

theorem empty_value : value base kernels (compile templates templates_valid empty) = 1 := by
  rw [value_compile templates templates_valid extension base kernels local_exact]
  decide

/-- The concrete run starts at original graph bytes and ends at the exposed output bytes. -/
def compiler_run : Turing.TM2OutputsInTime
    (computes templates templates_valid).machine.computer
    ((validatedEncoding 2 1 (sourceArity templates)).encode repeated)
    (some ((validatedEncoding 1 1 arity).encode output))
    ((computes templates templates_valid).time.eval
      ((validatedEncoding 2 1 (sourceArity templates)).encode repeated).length) :=
  (computes templates templates_valid).outputs repeated

/-- The additional finite table written against the common prefix arity function. -/
def extended (i : Fin 2) : Signature ℕ (arity i.val) := fun x =>
  if i.val = 0 then base 0 x else
    if x 0 then (if x 1 then 22 else 15) else (if x 1 then 10 else 7)

theorem extended_prefix (i : Fin 1) :
    extended ⟨i.val, by omega⟩ = base i := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rfl

theorem extended_realized (i : Fin 2) :
    HEq (macroSignatures templates templates_valid base kernels i) (extended i) := by
  rcases i with ⟨i, hi⟩
  have h : i = 0 ∨ i = 1 := by omega
  rcases h with rfl | rfl
  · change HEq (macroSignatures templates templates_valid base kernels (0 : Fin 2)) (extended 0)
    apply heq_of_eq
    decide
  · change HEq (macroSignatures templates templates_valid base kernels (1 : Fin 2)) (extended 1)
    apply heq_of_eq
    decide

/-- Both directions are witnessed by real finite machines. -/
theorem finite_resource_equivalent : Complexity.ParsimoniousEquivalent
    (validatedEncoding 2 1 arity) (validatedEncoding 1 1 arity)
    (value extended kernels) (value base kernels) :=
  extension_equivalent (by decide) templates boundaries templates_valid base extended kernels
    extended_prefix extended_realized

/-- A literal zero-valued nullary factor stays present as an isolated graph vertex. -/
def nullaryTemplates (_ : ℕ) : Template := ⟨0, [(0, [])], []⟩

theorem nullary_valid : ∀ i < 1, (nullaryTemplates i).WellFormed 1 0 (fun _ => 0) := by
  intro i _
  change (⟨0, [(0, [])], []⟩ : Template).WellFormed 1 0 (fun _ => 0)
  decide

def nullaryInput : Input 1 0 (sourceArity nullaryTemplates) := ⟨⟨[(0, [])], []⟩, by decide⟩

theorem nullary_output_record :
    (compile nullaryTemplates nullary_valid nullaryInput).val = ⟨[(0, [])], []⟩ := rfl

theorem nullary_zero_value :
    value (fun (_ : Fin 1) (_ : Fin 0 → Bool) => (0 : ℕ))
      (fun e : Fin 0 => Fin.elim0 e)
      (compile nullaryTemplates nullary_valid nullaryInput) = 0 := by decide
end
end Counting.Reduction.FixedGadget.Client
