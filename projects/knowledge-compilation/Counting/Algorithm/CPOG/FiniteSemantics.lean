import ProofChecker.Count.PropForm
import Mathlib.Data.Fintype.Pi

/-!
# Finite assignments and the original CPOG model sums

The declared variables are exactly the positive names `1, ..., n`.  A finite
Boolean assignment extends by `false` outside those names.  This gives an actual
bijection with the upstream finite set of supported assignments, including when
`n = 0`.  Model counts and complementary weighted model sums therefore agree
with sums over all `Fin n → Bool` assignments.

These are semantic identities.  No formula-variable containment, nonnegative
weight, machine representation, or running-time premise is imposed or inferred.
-/

open scoped BigOperators
open LeanSAT.Model

namespace Counting.Algorithm.CPOG.FiniteSemantics

/-- The explicitly declared variable names, including names absent from a formula. -/
def declared (n : ℕ) : Finset PNat :=
  Finset.univ.image (fun i : Fin n => Nat.succPNat i.val)

theorem variableName_injective (n : ℕ) :
    Function.Injective (fun i : Fin n => Nat.succPNat i.val) := by
  intro i j h
  exact Fin.ext (Nat.succPNat_injective h)

@[simp] theorem mem_declared (n : ℕ) (x : PNat) :
    x ∈ declared n ↔ x.natPred < n := by
  change x ∈ Finset.univ.image (fun i : Fin n => Nat.succPNat i.val) ↔ _
  constructor
  · rintro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    simpa only [Nat.natPred_succPNat] using i.isLt
  · intro hx
    exact Finset.mem_image.mpr
      ⟨⟨x.natPred, hx⟩, Finset.mem_univ _, PNat.succPNat_natPred x⟩

@[simp] theorem declared_card (n : ℕ) : (declared n).card = n := by
  change (Finset.univ.image (fun i : Fin n => Nat.succPNat i.val)).card = n
  rw [Finset.card_image_of_injective _ (variableName_injective n)]
  simp

/-- Extend a finite assignment by `false` on every undeclared positive name. -/
def extend {n : ℕ} (a : Fin n → Bool) : PropAssignment PNat :=
  fun x => if h : x.natPred < n then a ⟨x.natPred, h⟩ else false

@[simp] theorem extend_at {n : ℕ} (a : Fin n → Bool) (i : Fin n) :
    extend a (Nat.succPNat i.val) = a i := by
  have h : (Nat.succPNat i.val).natPred < n := by
    simpa only [Nat.natPred_succPNat] using i.isLt
  change (if h' : (Nat.succPNat i.val).natPred < n then
    a ⟨(Nat.succPNat i.val).natPred, h'⟩ else false) = a i
  rw [dite_eq_left h]
  congr 1

theorem extend_defined_on {n : ℕ} (a : Fin n → Bool) :
    (extend a).defined_on (declared n) := by
  intro x hx
  have hn : ¬x.natPred < n := fun h => hx ((mem_declared n x).mpr h)
  exact dite_eq_right hn

theorem extend_injective (n : ℕ) :
    Function.Injective (extend (n := n)) := by
  intro a b h
  funext i
  have hi := congr_fun h (Nat.succPNat i.val)
  simpa only [extend_at] using hi

/-- Read exactly the declared names of an upstream assignment. -/
def restrict {n : ℕ} (v : PropAssignment PNat) : Fin n → Bool :=
  fun i => v (Nat.succPNat i.val)

@[simp] theorem restrict_extend {n : ℕ} (a : Fin n → Bool) :
    restrict (extend a) = a := by
  funext i
  exact extend_at a i

theorem extend_restrict {n : ℕ} (v : PropAssignment PNat)
    (hv : v.defined_on (declared n)) : extend (restrict (n := n) v) = v := by
  funext x
  by_cases hx : x.natPred < n
  · change (if h : x.natPred < n then
      v (Nat.succPNat (⟨x.natPred, h⟩ : Fin n).val) else false) = v x
    rw [dite_eq_left hx, PNat.succPNat_natPred]
  · change (if h : x.natPred < n then
      v (Nat.succPNat (⟨x.natPred, h⟩ : Fin n).val) else false) = v x
    rw [dite_eq_right hx, hv (fun h => hx ((mem_declared n x).mp h))]

/-- The original supported assignments are exactly the finite Boolean assignments. -/
theorem assignments_eq_image (n : ℕ) :
    (declared n).assignments = Finset.univ.image (extend (n := n)) := by
  classical
  ext v
  rw [Finset.mem_assignments, Finset.mem_image]
  constructor
  · intro hv
    exact ⟨restrict v, Finset.mem_univ _, extend_restrict v hv⟩
  · rintro ⟨a, _, rfl⟩
    exact extend_defined_on a

/-- Change the index of any sum over the upstream supported assignments. -/
theorem sum_assignments {R : Type*} [AddCommMonoid R] (n : ℕ)
    (f : PropAssignment PNat → R) :
    (∑ v ∈ (declared n).assignments, f v) = ∑ a : Fin n → Bool, f (extend a) := by
  classical
  rw [assignments_eq_image, Finset.sum_image (extend_injective n).injOn]

/-- Count models without dropping declared but unused variables. -/
theorem models_card_eq_sum (n : ℕ) (φ : PropForm PNat) :
    (φ.models (declared n)).card =
      ∑ a : Fin n → Bool, if φ.eval (extend a) then 1 else 0 := by
  classical
  change ((declared n).assignments.filter (fun v => φ.eval v)).card = _
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, sum_assignments]

/-- The upstream assignment weight contains each declared variable exactly once. -/
theorem weight_product_extend {R : Type*} [CommRing R] {n : ℕ}
    (w : PNat → R) (a : Fin n → Bool) :
    (∏ x ∈ declared n, if extend a x then w x else 1 - w x) =
      ∏ i : Fin n, if a i then w (Nat.succPNat i.val) else 1 - w (Nat.succPNat i.val) := by
  classical
  change (∏ x ∈ Finset.univ.image (fun i : Fin n => Nat.succPNat i.val),
    if extend a x then w x else 1 - w x) = _
  rw [Finset.prod_image (variableName_injective n).injOn]
  simp only [extend_at]

/-- Complementary weighted models, with no sign or positivity restriction. -/
theorem weightSum_eq_sum {R : Type} [CommRing R] (n : ℕ)
    (w : PNat → R) (φ : PropForm PNat) :
    φ.weightSum w (declared n) =
      ∑ a : Fin n → Bool, if φ.eval (extend a) then
        ∏ i : Fin n, if a i then w (Nat.succPNat i.val) else 1 - w (Nat.succPNat i.val)
        else 0 := by
  classical
  change (∑ v ∈ (declared n).assignments.filter (fun v => φ.eval v),
    ∏ x ∈ declared n, if v x then w x else 1 - w x) = _
  rw [Finset.sum_filter, sum_assignments]
  simp only [weight_product_extend]

end Counting.Algorithm.CPOG.FiniteSemantics
