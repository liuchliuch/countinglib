/-
Vendored from ComplexCSP/Instances/Basic.lean at commit c454c2d6426cd8b9f9bcfd3e54bd69de1dcf48ec.
Source SHA-256: 50f08e3d338fe2784a1dcf6cbb69406c8b987f3a5bd0db8c2f47920e798be4df.
See provenance/ComplexCSP/source.json and notes/COMPLEXCSP.md.
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.List.OfFn

/-!
# Finite weighted constraint instances

Literal finite-instance semantics for Section 2.2 of arXiv:2608.14845v1.
Scopes are functions and can repeat variables. Constraints are lists, retaining
multiplicity. Boundary and hidden variables are kept separate, so taking a
boundary diagonal minor never identifies hidden variables or changes a sum.
-/
namespace ComplexCSP

/-- A finite language is indexed by a finite type; its actual table entries
are supplied, not postulated by an oracle. -/
structure Language (D : Type) (K : Type) (ι : Type) where
  arity : ι → ℕ
  arity_pos : ∀ i, 0 < arity i
  value : (i : ι) → (Fin (arity i) → D) → K

/-- An ordered scope, including repeated variables. -/
structure Constraint {D : Type} {K : Type} {ι : Type}
    (L : Language D K ι) (V : Type) where
  symbol : ι
  scope : Fin (L.arity symbol) → V

namespace Constraint
variable {D : Type} {K : Type} {ι : Type} {V W : Type}
variable {L : Language D K ι}

def rename (c : Constraint L V) (f : V → W) : Constraint L W :=
  ⟨c.symbol, f ∘ c.scope⟩

def eval (c : Constraint L V) (a : V → D) : K :=
  L.value c.symbol (a ∘ c.scope)

@[simp] theorem eval_rename (c : Constraint L V) (f : V → W) (a : W → D) :
    (c.rename f).eval a = c.eval (a ∘ f) := rfl
end Constraint

/-- A finite instance whose external variables are `B`, hidden variables `H`.
The list quotient by permutations is unnecessary for literal evaluation. -/
structure Instance {D : Type} {K : Type} {ι : Type}
    (L : Language D K ι) (B H : Type) where
  constraints : List (Constraint L (B ⊕ H))

namespace Instance
variable {D : Type} {K : Type} {ι : Type} {B C H : Type}
variable {L : Language D K ι}

def renameBoundary (I : Instance L B H) (f : B → C) : Instance L C H :=
  ⟨I.constraints.map (fun c => c.rename (Sum.map f id))⟩

def eval [CommMonoid K] (I : Instance L B H) (a : B → D) (b : H → D) : K :=
  (I.constraints.map (fun c => c.eval (Sum.elim a b))).prod

@[simp] theorem eval_renameBoundary [CommMonoid K]
    (I : Instance L B H) (f : B → C) (a : C → D) (b : H → D) :
    (I.renameBoundary f).eval a b = I.eval (a ∘ f) b := by
  simp only [eval, renameBoundary, List.map_map]
  congr 2
  funext c
  simp only [Function.comp_apply, Constraint.eval_rename]
  congr 1
  funext v
  cases v <;> rfl

/-- The pinned partition table, summing over every hidden-variable assignment.
This sum keeps exact cancellations. -/
def partition [CommSemiring K] [Fintype D] [Fintype H] [DecidableEq H]
    (I : Instance L B H) (a : B → D) : K :=
  ∑ b : H → D, I.eval a b

/-- The actual scope-renaming construction proves external diagonal minors.
No surjectivity is needed when new boundary variables are allowed to be isolated. -/
@[simp] theorem partition_renameBoundary [CommSemiring K] [Fintype D] [Fintype H] [DecidableEq H]
    (I : Instance L B H) (f : B → C) (a : C → D) :
    (I.renameBoundary f).partition a = I.partition (a ∘ f) := by
  simp only [partition, eval_renameBoundary]

variable {H₁ H₂ : Type}

def renameHidden (I : Instance L B H₁) (f : H₁ → H₂) : Instance L B H₂ :=
  ⟨I.constraints.map (fun c => c.rename (Sum.map id f))⟩

@[simp] theorem eval_renameHidden [CommMonoid K]
    (I : Instance L B H₁) (f : H₁ → H₂) (a : B → D) (b : H₂ → D) :
    (I.renameHidden f).eval a b = I.eval a (b ∘ f) := by
  simp only [eval, renameHidden, List.map_map]
  congr 2
  funext c
  simp only [Function.comp_apply, Constraint.eval_rename]
  congr 1
  funext v
  cases v <;> rfl

/-- Relabeling the hidden variables by a bijection preserves every exact marginal. -/
theorem partition_renameHidden_equiv [CommSemiring K] [Fintype D]
    [Fintype H₁] [Fintype H₂] [DecidableEq H₁] [DecidableEq H₂]
    (I : Instance L B H₁) (e : H₁ ≃ H₂) (a : B → D) :
    (I.renameHidden e).partition a = I.partition a := by
  simp only [partition, eval_renameHidden]
  exact (Equiv.arrowCongr e (Equiv.refl D)).symm.sum_comp (I.eval a)

/-- Glue two finite constraint instances, sharing the boundary and keeping the
hidden variables disjoint. Constraints are concatenated with their multiplicity. -/
def glue (I : Instance L B H₁) (J : Instance L B H₂) : Instance L B (H₁ ⊕ H₂) :=
  ⟨(I.renameHidden Sum.inl).constraints ++ (J.renameHidden Sum.inr).constraints⟩

@[simp] theorem eval_glue [CommMonoid K] (I : Instance L B H₁)
    (J : Instance L B H₂) (a : B → D) (b : H₁ ⊕ H₂ → D) :
    (I.glue J).eval a b = I.eval a (b ∘ Sum.inl) * J.eval a (b ∘ Sum.inr) := by
  simp only [eval, glue, List.map_append, List.prod_append]
  exact congrArg₂ (· * ·) (eval_renameHidden I (Sum.inl : H₁ → H₁ ⊕ H₂) a b)
    (eval_renameHidden J (Sum.inr : H₂ → H₁ ⊕ H₂) a b)

/-- Pinned partition values multiply under actual instance gluing. -/
theorem partition_glue [CommSemiring K] [Fintype D]
    [Fintype H₁] [Fintype H₂] [DecidableEq H₁] [DecidableEq H₂]
    (I : Instance L B H₁) (J : Instance L B H₂) (a : B → D) :
    (I.glue J).partition a = I.partition a * J.partition a := by
  simp only [partition, eval_glue]
  rw [Finset.sum_mul_sum]
  exact (Equiv.sumArrowEquivProdArrow H₁ H₂ D).sum_comp
    (fun b => I.eval a b.1 * J.eval a b.2) |>.trans
      (Fintype.sum_prod_type _)

/-- Move some boundary variables into the summed hidden part without identifying
any variables or changing any constraint occurrence. -/
def hideBoundary (I : Instance L (B ⊕ H₁) H₂) : Instance L B (H₁ ⊕ H₂) :=
  ⟨I.constraints.map (fun c => c.rename (Equiv.sumAssoc B H₁ H₂))⟩

@[simp] theorem eval_hideBoundary [CommMonoid K]
    (I : Instance L (B ⊕ H₁) H₂) (a : B → D) (b : H₁ ⊕ H₂ → D) :
    I.hideBoundary.eval a b = I.eval (Sum.elim a (b ∘ Sum.inl)) (b ∘ Sum.inr) := by
  simp only [eval, hideBoundary, List.map_map]
  congr 2
  funext c
  simp only [Function.comp_apply, Constraint.eval_rename]
  congr 1
  funext v
  rcases v with (v | v) | v <;> rfl

/-- Iterated marginalization is exactly a single larger finite sum. -/
theorem partition_hideBoundary [CommSemiring K] [Fintype D]
    [Fintype H₁] [Fintype H₂] [DecidableEq H₁] [DecidableEq H₂]
    (I : Instance L (B ⊕ H₁) H₂) (a : B → D) :
    I.hideBoundary.partition a = ∑ b : H₁ → D, I.partition (Sum.elim a b) := by
  simp only [partition, eval_hideBoundary]
  exact (Equiv.sumArrowEquivProdArrow H₁ H₂ D).sum_comp
    (fun b => I.eval (Sum.elim a b.1) b.2) |>.trans
      (Fintype.sum_prod_type _)

/-- Canonically encoded hidden variables, with unbounded finite size. -/
def Generated [CommSemiring K] [Fintype D] (L : Language D K ι)
    (G : (B → D) → K) : Prop :=
  ∃ n : ℕ, ∃ I : Instance L B (Fin n), ∀ a, I.partition a = G a

/-- Lemma 3.3, for literal generated-table witnesses. Taking `B = Fin r`,
`C = Fin s` and a surjection recovers exactly the paper's statement. -/
theorem generated_diagonal_minor [CommSemiring K] [Fintype D]
    {G : (B → D) → K} (hG : Generated L G) (f : B → C) :
    Generated L (fun a => G (a ∘ f)) := by
  obtain ⟨n, I, hI⟩ := hG
  exact ⟨n, I.renameBoundary f, fun a => by simp only [partition_renameBoundary, hI]⟩

/-- A finite hidden type can always be canonically encoded by `Fin n`. -/
theorem generated_partition [CommSemiring K] [Fintype D]
    [Fintype H] [DecidableEq H] (I : Instance L B H) :
    Generated L I.partition := by
  classical
  exact ⟨Fintype.card H, I.renameHidden (Fintype.equivFin H),
    fun a => partition_renameHidden_equiv I (Fintype.equivFin H) a⟩

/-- Generated tables are closed under pointwise multiplication via actual
finite-instance gluing, with disjoint hidden-variable copies. -/
theorem generated_mul [CommSemiring K] [Fintype D]
    {G F : (B → D) → K} (hG : Generated L G) (hF : Generated L F) :
    Generated L (fun a => G a * F a) := by
  obtain ⟨n, I, hI⟩ := hG
  obtain ⟨m, J, hJ⟩ := hF
  have h := generated_partition (I.glue J)
  have he : (I.glue J).partition = (fun a => G a * F a) := by
    funext a
    simp only [partition_glue, hI, hJ]
  rwa [he] at h

/-- The empty constraint instance with no hidden variables is the constant-one
boundary table. -/
theorem generated_one [CommSemiring K] [Fintype D] :
    Generated L (fun _ : B → D => (1 : K)) := by
  refine ⟨0, ⟨[]⟩, ?_⟩
  intro a
  simp [partition, eval]

/-- Lemma 8.1: every positive entrywise power has a finite-instance witness.
The zero power is also generated, by the empty constraint instance. -/
theorem generated_pow [CommSemiring K] [Fintype D]
    {G : (B → D) → K} (hG : Generated L G) (n : ℕ) :
    Generated L (fun a => G a ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (generated_one (B := B) (L := L))
  | succ n ih => simpa only [pow_succ] using generated_mul ih hG

/-- Generated tables remain generated after summing any finite block of retained
variables. Previously hidden variables stay distinct from the new hidden block. -/
theorem generated_marginal [CommSemiring K] [Fintype D]
    [Fintype H] [DecidableEq H] {G : (B ⊕ H → D) → K}
    (hG : Generated L G) : Generated L (fun a => ∑ b : H → D, G (Sum.elim a b)) := by
  obtain ⟨n, I, hI⟩ := hG
  have h := generated_partition I.hideBoundary
  have he : I.hideBoundary.partition = (fun a => ∑ b : H → D, G (Sum.elim a b)) := by
    funext a
    simp only [partition_hideBoundary, hI]
  rwa [he] at h

/-- A finite product of generated tables is generated by repeated gluing. -/
theorem generated_finset_prod [CommSemiring K] [Fintype D] {α : Type}
    (s : Finset α) (G : α → (B → D) → K) (hG : ∀ i ∈ s, Generated L (G i)) :
    Generated L (fun a => ∏ i ∈ s, G i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (generated_one (B := B) (L := L))
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      generated_mul (hG i (Finset.mem_insert_self i s))
        (ih (fun j hj => hG j (Finset.mem_insert_of_mem hj)))

end Instance
end ComplexCSP
