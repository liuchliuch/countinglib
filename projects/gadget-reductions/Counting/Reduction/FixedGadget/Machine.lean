import Counting.Reduction.FixedGadget.Basic
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Compile
import Holant.Complexity.FixedGadgetSubstitution.Size
import Counting.Complexity.Reduction

/-! The canonical compiler's actual byte machine, natural count reduction, and
correctly directed FP/hardness transports. -/
namespace Counting.Reduction.FixedGadget
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Computability RawClosedNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {sourceCount s b : ℕ} {arity : ℕ → ℕ}
variable (templates : ℕ → Template)
variable (hg : ∀ i < sourceCount, (templates i).WellFormed s b arity)

/-- Compile original input bytes to literal output bytes with a clean finite TM2. -/
def computes : BinaryCompose.Computes
    (validatedEncoding sourceCount b (sourceArity templates))
    (validatedEncoding s b arity) (compile templates hg) :=
  Compiler.computes sourceCount b (sourceArity templates) templates s arity
    (fun i hi => ⟨hg i hi, rfl⟩)

theorem compiler_inFP : InFP (validatedEncoding sourceCount b (sourceArity templates))
    (validatedEncoding s b arity) (compile templates hg) :=
  (computes templates hg).inFP

/-- Materialized encoded output length follows from the actual finite program. -/
theorem output_length (r : Input sourceCount b (sourceArity templates)) :
    ((validatedEncoding s b arity).encode (compile templates hg r)).length ≤
      (Computation.PolyTime.outputLengthPolynomial (computes templates hg).toPolyTime).eval
        ((validatedEncoding sourceCount b (sourceArity templates)).encode r).length :=
  Computation.PolyTime.encoded_output_length_le (computes templates hg).toPolyTime r

/-- The sharper static bound still measures the original input's encoded bits. -/
theorem output_length_static (A V E : ℕ) (ha : ∀ i < s, arity i ≤ A)
    (hb : ∀ i < sourceCount, (templates i).vertices.length ≤ V ∧
      (templates i).edges.length ≤ E)
    (r : Input sourceCount b (sourceArity templates)) :
    ((validatedEncoding s b arity).encode (compile templates hg r)).length ≤
      (querySizePolynomial s b A V E).eval
        ((validatedEncoding sourceCount b (sourceArity templates)).encode r).length :=
  replace_length_le templates r.val r.property (fun i hi => ⟨hg i hi, rfl⟩) A V E ha hb

/-- Elementary Boolean instruction cost of that very compiler run. -/
theorem primitive_bound (r : Input sourceCount b (sourceArity templates)) :
    FixedFieldMachines.primitiveCost (computes templates hg).machine
      ((computes templates hg).outputs r).steps
      (some (Turing.initList (computes templates hg).machine.computer
        ((validatedEncoding sourceCount b (sourceArity templates)).encode r))) ≤
      (FixedFieldMachines.primitivePolynomial (computes templates hg)).eval
        ((validatedEncoding sourceCount b (sourceArity templates)).encode r).length :=
  Compiler.primitive_bound sourceCount b (sourceArity templates) templates s arity
    (fun i hi => ⟨hg i hi, rfl⟩) r

/-- Naturals have a parsimonious reduction; no complex output is retyped as a count. -/
def parsimonious
    (source : (i : Fin sourceCount) → Signature ℕ (sourceArity templates i.val))
    (signatures : (i : Fin s) → Signature ℕ (arity i.val))
    (kernels : Fin b → Bool → Bool → ℕ)
    (hlocal : ∀ i, macroSignatures templates hg signatures kernels i = source i) :
    Complexity.ParsimoniousReduction
      (validatedEncoding sourceCount b (sourceArity templates))
      (validatedEncoding s b arity) (value source kernels) (value signatures kernels) where
  map := compile templates hg
  machine := (computes templates hg).toPolyTime
  correct r := (value_compile templates hg source signatures kernels hlocal r).symm

/-- A base evaluator computes the extended problem by the proved compiler. -/
theorem inFP_of_base {R Γ : Type} [CommSemiring R] [Fintype Γ]
    (answerEncoding : Encoding R Γ)
    (source : (i : Fin sourceCount) → Signature R (sourceArity templates i.val))
    (signatures : (i : Fin s) → Signature R (arity i.val))
    (kernels : Fin b → Bool → Bool → R)
    (hlocal : ∀ i, macroSignatures templates hg signatures kernels i = source i)
    (base : InFP (validatedEncoding s b arity) answerEncoding (value signatures kernels)) :
    InFP (validatedEncoding sourceCount b (sourceArity templates)) answerEncoding
      (value source kernels) :=
  Computation.InFP.congr (Computation.InFP.comp (compiler_inFP templates hg) base)
    (value_compile templates hg source signatures kernels hlocal)

/-- Hardness of the extended natural-count problem propagates to the base problem. -/
theorem hard_base_of_extension {α Γ : Type} [Fintype Γ]
    (inputEncoding : Encoding α Γ) (C : (α → ℕ) → Prop)
    (source : (i : Fin sourceCount) → Signature ℕ (sourceArity templates i.val))
    (signatures : (i : Fin s) → Signature ℕ (arity i.val))
    (kernels : Fin b → Bool → Bool → ℕ)
    (hlocal : ∀ i, macroSignatures templates hg signatures kernels i = source i)
    (hard : Complexity.HardFor inputEncoding
      (validatedEncoding sourceCount b (sourceArity templates)) C (value source kernels)) :
    Complexity.HardFor inputEncoding (validatedEncoding s b arity) C
      (value signatures kernels) :=
  hard.transportReduction (parsimonious templates hg source signatures kernels hlocal)
end
end Counting.Reduction.FixedGadget
