import Holant.Complexity.FixedGadgetSubstitution.Partition

/-! Exact fixed-template substitution on the canonical ordered Holant graph.
The only semantic premises are local fixed gadget identities. -/
namespace Counting.Reduction.FixedGadget
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open RawClosedNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {sourceCount s b : ℕ} {arity : ℕ → ℕ}

/-- The runtime input is the original validated graph, including ordered records. -/
abbrev Input (count b : ℕ) (arity : ℕ → ℕ) :=
  {r : RawClosedNetwork // r.WellFormed count b arity}

/-- Literal replacement. The template family, labels, and arities are fixed. -/
def compile (templates : ℕ → Template)
    (hg : ∀ i < sourceCount, (templates i).WellFormed s b arity)
    (r : Input sourceCount b (sourceArity templates)) : Input s b arity :=
  ⟨replace templates r.val, query_wellFormed templates r.val r.property hg⟩

@[simp] theorem compile_raw (templates : ℕ → Template)
    (hg : ∀ i < sourceCount, (templates i).WellFormed s b arity)
    (r : Input sourceCount b (sourceArity templates)) :
    (compile templates hg r).val = replace templates r.val := rfl

/-- The original closed-network evaluation, without recovery or normalization. -/
def value {R : Type} [CommSemiring R]
    (signatures : (i : Fin s) → Signature R (arity i.val))
    (kernels : Fin b → Bool → Bool → R) (r : Input s b arity) : R :=
  (r.val.realize r.property signatures kernels).denote Fin.elim0

/-- Actual macro signatures obtained by summing the fixed template's internal ends. -/
def macroSignatures {R : Type} [CommSemiring R]
    (templates : ℕ → Template)
    (hg : ∀ i < sourceCount, (templates i).WellFormed s b arity)
    (signatures : (i : Fin s) → Signature R (arity i.val))
    (kernels : Fin b → Bool → Bool → R) (i : Fin sourceCount) :
    Signature R (sourceArity templates i.val) :=
  ((templates i.val).network (hg i.val i.isLt) signatures kernels).denote

/-- Exact local realization implies global equality on the actual compiler output. -/
theorem value_compile {R : Type} [CommSemiring R]
    (templates : ℕ → Template)
    (hg : ∀ i < sourceCount, (templates i).WellFormed s b arity)
    (source : (i : Fin sourceCount) → Signature R (sourceArity templates i.val))
    (signatures : (i : Fin s) → Signature R (arity i.val))
    (kernels : Fin b → Bool → Bool → R)
    (hlocal : ∀ i, macroSignatures templates hg signatures kernels i = source i)
    (r : Input sourceCount b (sourceArity templates)) :
    value signatures kernels (compile templates hg r) = value source kernels r := by
  have h := replacement_partition templates r.val r.property hg source signatures kernels
    (fun _ => 1) (by intro i; simpa [macroSignatures] using hlocal i)
  simpa only [value, compile, Finset.prod_const_one, one_mul] using h

/-- A family of actual macros always satisfies the local realization obligations. -/
theorem value_compile_macros {R : Type} [CommSemiring R]
    (templates : ℕ → Template)
    (hg : ∀ i < sourceCount, (templates i).WellFormed s b arity)
    (signatures : (i : Fin s) → Signature R (arity i.val))
    (kernels : Fin b → Bool → Bool → R)
    (r : Input sourceCount b (sourceArity templates)) :
    value signatures kernels (compile templates hg r) =
      value (macroSignatures templates hg signatures kernels) kernels r :=
  value_compile templates hg _ signatures kernels (fun _ => rfl) r

end
end Counting.Reduction.FixedGadget
