import Counting.Model.Basic
import Mathlib.Logic.Equiv.Set

/-! Boundary-complement assignments. No default element of the value domain is used. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Counting.Bridge.OpenNetwork.BoundaryComplement

variable {B P D R : Type}

/-- Ports outside the image of the supplied injective boundary map. -/
def Hidden (b : B ↪ P) := {p : P // p ∉ Set.range b}

instance [Fintype P] (b : B ↪ P) : Fintype (Hidden b) :=
  inferInstanceAs (Fintype {p : P // p ∉ Set.range b})

instance (b : B ↪ P) : DecidableEq (Hidden b) := Classical.decEq _

/-- Split ports into the actual ordered boundary and its complement. -/
def ports (b : B ↪ P) : B ⊕ Hidden b ≃ P := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective b b.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun p => p ∈ Set.range b))

@[simp] theorem ports_boundary (b : B ↪ P) (j : B) : ports b (.inl j) = b j := rfl
@[simp] theorem ports_hidden (b : B ↪ P) (h : Hidden b) : ports b (.inr h) = h.val := rfl

/-- Extend a supplied boundary word with a hidden assignment. -/
def extend (b : B ↪ P) (x : B → D) (h : Hidden b → D) : P → D :=
  fun p => Sum.elim x h ((ports b).symm p)

@[simp] theorem extend_boundary (b : B ↪ P) (x : B → D) (h : Hidden b → D) (j : B) :
    extend b x h (b j) = x j := by
  change Sum.elim x h ((ports b).symm (ports b (.inl j))) = _
  simp only [Equiv.symm_apply_apply, Sum.elim_inl]

@[simp] theorem extend_hidden (b : B ↪ P) (x : B → D) (h : Hidden b → D) (p : Hidden b) :
    extend b x h p.val = h p := by
  change Sum.elim x h ((ports b).symm (ports b (.inr p))) = _
  simp only [Equiv.symm_apply_apply, Sum.elim_inr]

/-- Every complete assignment splits uniquely into boundary and hidden words. -/
def assignments (b : B ↪ P) : (P → D) ≃ ((B → D) × (Hidden b → D)) where
  toFun z := (fun j => z (b j), fun h => z h.val)
  invFun q := extend b q.1 q.2
  left_inv z := by
    funext p
    obtain ⟨p, rfl⟩ := (ports b).surjective p
    cases p <;> simp
  right_inv q := by
    rcases q with ⟨x, h⟩
    apply Prod.ext <;> funext j <;> simp

/-- The promised explicit bijection with complete assignments satisfying the pins. -/
def compatibleAssignments (b : B ↪ P) (x : B → D) :
    (Hidden b → D) ≃ {z : P → D // ∀ j, z (b j) = x j} where
  toFun h := ⟨extend b x h, extend_boundary b x h⟩
  invFun z := fun h => z.val h.val
  left_inv h := by funext p; exact extend_hidden b x h p
  right_inv z := by
    apply Subtype.ext
    funext p
    obtain ⟨p, rfl⟩ := (ports b).surjective p
    cases p with
    | inl j => simpa using (z.property j).symm
    | inr h => simp

/-- Removing the boundary predicate is exact, even when the domain is empty. -/
theorem sum_extend [Fintype B] [Fintype P] [Fintype D] [CommSemiring R]
    (b : B ↪ P) (x : B → D) (w : (P → D) → R) :
    (∑ h : Hidden b → D, w (extend b x h)) =
      ∑ z : P → D, if ∀ j, z (b j) = x j then w z else 0 := by
  classical
  symm
  rw [← (assignments (D := D) b).symm.sum_comp
    (fun z => if ∀ j, z (b j) = x j then w z else 0), Fintype.sum_prod_type]
  have hp (y : B → D) (h : Hidden b → D) :
      (∀ j, extend b y h (b j) = x j) ↔ y = x := by
    simp only [extend_boundary, funext_iff]
  change (∑ y : B → D, ∑ h : Hidden b → D,
    if ∀ j, extend b y h (b j) = x j then w (extend b y h) else 0) = _
  simp only [hp]
  rw [Finset.sum_comm]
  simp

end Counting.Bridge.OpenNetwork.BoundaryComplement
