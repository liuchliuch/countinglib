import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum

/-!
# Finite assignment sums

These identities split sums over assignments to disjoint variable sets. They
retain assignments to every variable, including isolated variables, and allow an
empty domain. The additive identities need only an additive commutative monoid;
independent-product factorization uses a commutative semiring.
-/

namespace Counting.Model.FiniteSums

open scoped BigOperators

variable {B D R H1 H2 H3 : Type}
variable [Fintype D] [Fintype H1] [Fintype H2]
variable [DecidableEq H1] [DecidableEq H2]

section Additive

variable [AddCommMonoid R]

/-- An assignment on a disjoint union is exactly a pair of assignments. -/
theorem sum_sum_assignments (f : (H1 ⊕ H2 → D) → R) :
    (∑ h : H1 ⊕ H2 → D, f h) =
      ∑ h1 : H1 → D, ∑ h2 : H2 → D, f (Sum.elim h1 h2) := by
  calc
    (∑ h : H1 ⊕ H2 → D, f h) =
        ∑ p : (H1 → D) × (H2 → D), f (Sum.elim p.1 p.2) :=
      ((Equiv.sumArrowEquivProdArrow H1 H2 D).symm.sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

/-- Splitting three sets of variables yields the same ordered triple sum. -/
theorem sum_sum_assignments_assoc [Fintype H3] [DecidableEq H3]
    (f : ((H1 ⊕ H2) ⊕ H3 → D) → R) :
    (∑ h : (H1 ⊕ H2) ⊕ H3 → D, f h) =
      ∑ h1 : H1 → D, ∑ h2 : H2 → D, ∑ h3 : H3 → D,
        f (Sum.elim (Sum.elim h1 h2) h3) := by
  rw [sum_sum_assignments, sum_sum_assignments]

/-- Partial summation is associative after reassociating the variable sets.
The fixed boundary `B` need not be finite. -/
theorem sum_partial_assoc (f : ((B ⊕ H1) ⊕ H2 → D) → R) (a : B → D) :
    (∑ h1 : H1 → D, ∑ h2 : H2 → D,
      f (Sum.elim (Sum.elim a h1) h2)) =
      ∑ h : H1 ⊕ H2 → D, f (Sum.elim a h ∘ Equiv.sumAssoc B H1 H2) := by
  symm
  rw [sum_sum_assignments]
  apply Finset.sum_congr rfl
  intro h1 _
  apply Finset.sum_congr rfl
  intro h2 _
  congr 1
  funext x
  rcases x with (b | h1') | h2' <;> rfl

end Additive

/-- Independent factors on disjoint sets of variables have a product partition
sum. No assumption that the assignment domain is inhabited is needed. -/
theorem sum_independent_mul [CommSemiring R]
    (f : (H1 → D) → R) (g : (H2 → D) → R) :
    (∑ h : H1 ⊕ H2 → D,
      f (fun x => h (Sum.inl x)) * g (fun x => h (Sum.inr x))) =
      (∑ h1 : H1 → D, f h1) * (∑ h2 : H2 → D, g h2) := by
  rw [sum_sum_assignments]
  exact (Fintype.sum_mul_sum f g).symm

end Counting.Model.FiniteSums
