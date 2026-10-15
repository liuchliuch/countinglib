import Counting.Reduction.FixedGadget.Machine

/-! Inclusion and elimination use the same finite graph codec. The base and
extension share an arity function on their label prefix; extra labels have their
explicit entries in that function. This is separate from RootCode languages. -/
namespace Counting.Reduction.FixedGadget
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Computability RawClosedNetwork
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {s t b : ℕ} {arity : ℕ → ℕ}

def includePrefix (hst : s ≤ t) (r : Input s b arity) : Input t b arity :=
  ⟨r.val, ⟨fun v => ⟨lt_of_lt_of_le (r.property.1 v).1 hst, (r.property.1 v).2⟩,
    r.property.2⟩⟩

@[simp] theorem includePrefix_bits (hst : s ≤ t) (r : Input s b arity) :
    (validatedEncoding t b arity).encode (includePrefix hst r) =
      (validatedEncoding s b arity).encode r := rfl

/-- Inclusion is the actual one-transition identity machine on unchanged bytes. -/
def includePrefixPolyTime (hst : s ≤ t) :
    PolyTime (validatedEncoding s b arity) (validatedEncoding t b arity) (includePrefix hst) where
  tm := (identityPolyTime (validatedEncoding s b arity)).tm
  inputAlphabet := (identityPolyTime (validatedEncoding s b arity)).inputAlphabet
  outputAlphabet := (identityPolyTime (validatedEncoding s b arity)).outputAlphabet
  time := 1
  outputsFun r := (identityPolyTime (validatedEncoding s b arity)).outputsFun r
  finiteAlphabets := (identityPolyTime (validatedEncoding s b arity)).finiteAlphabets

theorem value_includePrefix {R : Type} [CommSemiring R] (hst : s ≤ t)
    (base : (i : Fin s) → Signature R (arity i.val))
    (extension : (i : Fin t) → Signature R (arity i.val))
    (kernels : Fin b → Bool → Bool → R)
    (hprefix : ∀ i : Fin s, extension ⟨i.val, lt_of_lt_of_le i.isLt hst⟩ = base i)
    (r : Input s b arity) :
    value extension kernels (includePrefix hst r) = value base kernels r := by
  unfold value Network.denote
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro v _
    change extension ⟨(r.val.vertices.get v).1, _⟩ _ = base ⟨(r.val.vertices.get v).1, _⟩ _
    rw [hprefix ⟨(r.val.vertices.get v).1, (r.property.1 v).1⟩]
    rfl
  · rfl

/-- Every original natural-count instance includes without changing its answer. -/
def includePrefixParsimonious (hst : s ≤ t)
    (base : (i : Fin s) → Signature ℕ (arity i.val))
    (extension : (i : Fin t) → Signature ℕ (arity i.val))
    (kernels : Fin b → Bool → Bool → ℕ)
    (hprefix : ∀ i : Fin s, extension ⟨i.val, lt_of_lt_of_le i.isLt hst⟩ = base i) :
    Complexity.ParsimoniousReduction (validatedEncoding s b arity) (validatedEncoding t b arity)
      (value base kernels) (value extension kernels) where
  map := includePrefix hst
  machine := includePrefixPolyTime hst
  correct r := (value_includePrefix hst base extension kernels hprefix r).symm

/-- Finite exact adjunction is FP-equivalent in this original coefficient/count
model. The premises specify only fixed arities and local tables, not compiler cost. -/
theorem extension_inFP_iff {R Γ : Type} [CommSemiring R] [Fintype Γ]
    (answerEncoding : Encoding R Γ) (hst : s ≤ t)
    (templates : ℕ → Template)
    (hboundary : sourceArity templates = arity)
    (hg : ∀ i < t, (templates i).WellFormed s b arity)
    (base : (i : Fin s) → Signature R (arity i.val))
    (extension : (i : Fin t) → Signature R (arity i.val))
    (kernels : Fin b → Bool → Bool → R)
    (hprefix : ∀ i : Fin s, extension ⟨i.val, lt_of_lt_of_le i.isLt hst⟩ = base i)
    (hlocal : ∀ i : Fin t, HEq (macroSignatures templates hg base kernels i) (extension i)) :
    InFP (validatedEncoding t b arity) answerEncoding (value extension kernels) ↔
      InFP (validatedEncoding s b arity) answerEncoding (value base kernels) := by
  constructor
  · intro h
    exact Computation.InFP.congr
      (Computation.InFP.comp ⟨includePrefixPolyTime hst⟩ h)
      (value_includePrefix hst base extension kernels hprefix)
  · intro h
    subst arity
    exact inFP_of_base templates hg answerEncoding extension base kernels
      (fun i => eq_of_heq (hlocal i)) h

/-- The natural-valued formulation has actual parsimonious maps in both directions. -/
theorem extension_equivalent (hst : s ≤ t) (templates : ℕ → Template)
    (hboundary : sourceArity templates = arity)
    (hg : ∀ i < t, (templates i).WellFormed s b arity)
    (base : (i : Fin s) → Signature ℕ (arity i.val))
    (extension : (i : Fin t) → Signature ℕ (arity i.val))
    (kernels : Fin b → Bool → Bool → ℕ)
    (hprefix : ∀ i : Fin s, extension ⟨i.val, lt_of_lt_of_le i.isLt hst⟩ = base i)
    (hlocal : ∀ i : Fin t, HEq (macroSignatures templates hg base kernels i) (extension i)) :
    Complexity.ParsimoniousEquivalent (validatedEncoding t b arity) (validatedEncoding s b arity)
      (value extension kernels) (value base kernels) := by
  subst arity
  exact ⟨⟨parsimonious templates hg extension base kernels (fun i => eq_of_heq (hlocal i))⟩,
    ⟨includePrefixParsimonious hst base extension kernels hprefix⟩⟩

/-- Class-relative natural-count hardness is equivalent in the two supported
finite languages, with each implication using its actual reduction direction. -/
theorem extension_hard_iff {α Γ : Type} [Fintype Γ]
    (inputEncoding : Encoding α Γ) (C : (α → ℕ) → Prop)
    (hst : s ≤ t) (templates : ℕ → Template)
    (hboundary : sourceArity templates = arity)
    (hg : ∀ i < t, (templates i).WellFormed s b arity)
    (base : (i : Fin s) → Signature ℕ (arity i.val))
    (extension : (i : Fin t) → Signature ℕ (arity i.val))
    (kernels : Fin b → Bool → Bool → ℕ)
    (hprefix : ∀ i : Fin s, extension ⟨i.val, lt_of_lt_of_le i.isLt hst⟩ = base i)
    (hlocal : ∀ i : Fin t, HEq (macroSignatures templates hg base kernels i) (extension i)) :
    Complexity.HardFor inputEncoding (validatedEncoding t b arity) C (value extension kernels) ↔
      Complexity.HardFor inputEncoding (validatedEncoding s b arity) C (value base kernels) := by
  have eqv := extension_equivalent hst templates hboundary hg base extension kernels hprefix hlocal
  exact ⟨fun h => h.transport eqv.1, fun h => h.transport eqv.2⟩
end
end Counting.Reduction.FixedGadget
