import Holant.Complexity.Encoding
import PlanarHom.MachineComposition

/-!
# Polynomial time for faithful encodings on finite machines

The public predicate is the locked Holant finite-alphabet extension of mathlib's
actual TM2 transition semantics. Composition uses the ported PlanarHom syntax
compiler and its exact-run simulation, including an output-length cost bound.
-/

namespace Counting.Computation

open Computability

/-- A concrete finite-control TM2 computer with finite alphabets on every stack,
faithful external encodings, and a proved natural-coefficient time polynomial. -/
abbrev PolyTime {α β Γ₀ Γ₁ : Type} [Fintype Γ₀] [Fintype Γ₁]
    (ea : Encoding α Γ₀) (eb : Encoding β Γ₁) (f : α → β) :=
  Holant.Complexity.PolyTime ea eb f

/-- Existence of a concrete polynomial-time finite-machine implementation. -/
abbrev InFP {α β Γ₀ Γ₁ : Type} [Fintype Γ₀] [Fintype Γ₁]
    (ea : Encoding α Γ₀) (eb : Encoding β Γ₁) (f : α → β) : Prop :=
  Holant.Complexity.InFP ea eb f

namespace PolyTime

variable {α β γ Γ₀ Γ₁ Γ₂ : Type} [Fintype Γ₀] [Fintype Γ₁] [Fintype Γ₂]
    {ea : Encoding α Γ₀} {eb : Encoding β Γ₁} {ec : Encoding γ Γ₂}
    {f : α → β} {g : β → γ}

/-- A real one-transition machine computing the identity. -/
noncomputable def identity (e : Encoding α Γ₀) : PolyTime e e id :=
  Holant.Complexity.identityPolyTime e

/-- The syntax-derived output-size polynomial of a concrete implementation. -/
noncomputable def outputLengthPolynomial (hf : PolyTime ea eb f) : Polynomial ℕ :=
  PlanarHom.MachineComposition.outputLengthPolynomial hf.toTM2ComputableInPolyTime

/-- Materializing an encoded output is charged to the running time and the
constant number of pushes allowed by the finite program text. -/
theorem encoded_output_length_le (hf : PolyTime ea eb f) (a : α) :
    (eb.encode (f a)).length ≤ (outputLengthPolynomial hf).eval (ea.encode a).length :=
  PlanarHom.MachineComposition.encoded_output_length_le hf.toTM2ComputableInPolyTime a

/-- Compile two genuine finite machines into one. The first output and the second
input share a stack; the compiler proves the intermediate handoff and exact final
configuration, and derives the composed polynomial from an output-length bound. -/
noncomputable def comp (hf : PolyTime ea eb f) (hg : PolyTime eb ec g) :
    PolyTime ea ec (g ∘ f) := by
  letI := hf.finiteAlphabets
  letI := hg.finiteAlphabets
  exact {
    toTM2ComputableInPolyTime := PlanarHom.MachineComposition.composeComputers
      hf.toTM2ComputableInPolyTime hg.toTM2ComputableInPolyTime
    finiteAlphabets := PlanarHom.MachineComposition.sequentialAlphabetFintype hf.tm hg.tm
      (hf.outputAlphabet.trans hg.inputAlphabet.symm) }

/-- The exposed time bound charges the second computation at the proved bound on
the length of the first computation's materialized output. -/
@[simp] theorem comp_time (hf : PolyTime ea eb f) (hg : PolyTime eb ec g) :
    (comp hf hg).time = hg.time.comp (outputLengthPolynomial hf) + hf.time := rfl

/-- The constructed execution contains exactly the two original transition counts. -/
@[simp] theorem comp_steps (hf : PolyTime ea eb f) (hg : PolyTime eb ec g) (a : α) :
    ((comp hf hg).outputsFun a).steps =
      (hg.outputsFun (f a)).steps + (hf.outputsFun a).steps := rfl

end PolyTime

namespace InFP

variable {α β γ Γ₀ Γ₁ Γ₂ : Type} [Fintype Γ₀] [Fintype Γ₁] [Fintype Γ₂]
    {ea : Encoding α Γ₀} {eb : Encoding β Γ₁} {ec : Encoding γ Γ₂}
    {f : α → β} {g : β → γ}

/-- FP contains identity under any fixed faithful encoding. -/
theorem identity (e : Encoding α Γ₀) : InFP e e id := ⟨PolyTime.identity e⟩

/-- FP is closed under composition by the proved finite-machine compiler. -/
theorem comp (hf : InFP ea eb f) (hg : InFP eb ec g) : InFP ea ec (g ∘ f) := by
  obtain ⟨hf⟩ := hf
  obtain ⟨hg⟩ := hg
  exact ⟨PolyTime.comp hf hg⟩

/-- Pointwise equality transports membership without changing the machine. -/
theorem congr {f' : α → β} (hf : InFP ea eb f) (h : ∀ x, f x = f' x) :
    InFP ea eb f' := by
  have he : f = f' := funext h
  subst f'
  exact hf

end InFP

end Counting.Computation
