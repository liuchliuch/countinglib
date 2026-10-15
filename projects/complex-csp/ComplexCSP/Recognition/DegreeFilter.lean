import ComplexCSP.Instances.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Cyclic filtering of actual variable occurrence degrees

Occurrence lists retain repeated scope positions and repeated constraints.
The root-of-unity filter is derived from primitive-root identities and finite
sum factorization, not assumed as an oracle about generated instances.
-/

namespace ComplexCSP

open scoped BigOperators

/-- Orthogonality of a finite cyclic character, including degree zero and δ=1. -/
theorem cyclic_degree_sum {K : Type*} [Field K] {δ : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ δ) (d : ℕ) :
    (∑ t : Fin δ, ζ ^ (t.val * d)) = if δ ∣ d then (δ : K) else 0 := by
  classical
  by_cases hd : δ ∣ d
  · rw [if_pos hd]
    have hp : ζ ^ d = 1 := (hζ.pow_eq_one_iff_dvd d).mpr hd
    simp only [Nat.mul_comm _ d, pow_mul, hp, one_pow, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  · rw [if_neg hd]
    have hp : ζ ^ d ≠ 1 := fun h => hd ((hζ.pow_eq_one_iff_dvd d).mp h)
    have hpow : (ζ ^ d) ^ δ = 1 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    have hz : (∑ t ∈ Finset.range δ, (ζ ^ d) ^ t) = 0 := by
      apply eq_zero_of_ne_zero_of_mul_left_eq_zero (sub_ne_zero_of_ne hp.symm)
      rw [mul_neg_geom_sum, hpow, sub_self]
    simpa only [← Fin.sum_univ_eq_sum_range, ← pow_mul, Nat.mul_comm d] using hz

/-- A product over a list can be regrouped by exact occurrence counts. -/
theorem list_prod_by_count {V K : Type*} [Fintype V] [DecidableEq V] [CommMonoid K]
    (l : List V) (f : V → K) :
    (l.map f).prod = ∏ v, f v ^ l.count v := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hpow (v : V) : f v ^ (a :: l).count v =
        (if v = a then f a else 1) * f v ^ l.count v := by
      by_cases h : v = a
      · subst v
        simp [pow_succ, mul_comm]
      · simp [h, Ne.symm h]
    simp only [List.map_cons, List.prod_cons, ih, hpow, Finset.prod_mul_distrib]
    simp

namespace Instance

variable {D K ι B H : Type} {L : Language D K ι}

/-- All variable occurrences, in order. A scope mentioning a variable twice
contributes twice; a repeated constraint contributes all its positions again. -/
def occurrences (I : Instance L B H) : List (B ⊕ H) :=
  I.constraints.flatMap fun c => List.ofFn c.scope

/-- Actual occurrence degree, including the zero degree of isolated variables. -/
def occurrenceDegree [DecidableEq B] [DecidableEq H] (I : Instance L B H)
    (v : B ⊕ H) : ℕ := @List.count (B ⊕ H) instBEqOfDecidableEq v I.occurrences

/-- Regrouping auxiliary cyclic weights by the occurrence degree. -/
theorem auxiliary_weight_by_degree [CommMonoid K] [Fintype B] [Fintype H]
    [DecidableEq B] [DecidableEq H] (I : Instance L B H) (ζ : K)
    {δ : ℕ} (θ : (B ⊕ H) → Fin δ) :
    (I.occurrences.map (fun v => ζ ^ (θ v).val)).prod =
      ∏ v, ζ ^ ((θ v).val * I.occurrenceDegree v) := by
  rw [list_prod_by_count]
  simp only [occurrenceDegree, pow_mul]

end Instance

namespace Language

variable {D K ι : Type} [CommSemiring K]

/-- Attach a cyclic coordinate to every domain element and multiply each table
entry by one root power for every argument position. -/
def degreeAugment (L : Language D K ι) (δ : ℕ) (ζ : K) : Language (D × Fin δ) K ι where
  arity := L.arity
  arity_pos := L.arity_pos
  value i a := L.value i (fun t => (a t).1) * ∏ t, ζ ^ (a t).2.val

/-- An augmented entry is zero exactly when its original entry is, provided
the auxiliary root is nonzero. This justifies zero-pattern preservation. -/
theorem degreeAugment_value_eq_zero_iff [NoZeroDivisors K] [Nontrivial K] (L : Language D K ι)
    (δ : ℕ) {ζ : K} (hζ : ζ ≠ 0) (i : ι)
    (a : Fin (L.arity i) → D × Fin δ) :
    (L.degreeAugment δ ζ).value i a = 0 ↔
      L.value i (fun t => (a t).1) = 0 := by
  change L.value i (fun t => (a t).1) * (∏ t, ζ ^ (a t).2.val) = 0 ↔ _
  rw [mul_eq_zero]
  have hp : (∏ t, ζ ^ (a t).2.val) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun _ _ => pow_ne_zero _ hζ)
  simp only [hp, or_false]

/-- At positive cyclic size, the augmented table is identically zero iff the
original table is. The reverse direction uses the all-zero cyclic assignment. -/
theorem degreeAugment_zero_table_iff (L : Language D K ι)
    {δ : ℕ} (hδ : 0 < δ) (ζ : K) (i : ι) :
    (∀ a, (L.degreeAugment δ ζ).value i a = 0) ↔
      ∀ a, L.value i a = 0 := by
  constructor
  · intro h a
    simpa [degreeAugment] using h (fun t => (a t, (⟨0, hδ⟩ : Fin δ)))
  · intro h a
    simp [degreeAugment, h]

end Language

namespace Constraint

variable {D K ι V : Type} [CommSemiring K] {L : Language D K ι}

def degreeAugment (c : Constraint L V) (δ : ℕ) (ζ : K) :
    Constraint (L.degreeAugment δ ζ) V := ⟨c.symbol, c.scope⟩

end Constraint

namespace Instance

variable {D K ι B H : Type} [CommSemiring K] {L : Language D K ι}

/-- The degree-augmented instance preserves all scopes and multiplicities. -/
def degreeAugment (I : Instance L B H) (δ : ℕ) (ζ : K) :
    Instance (L.degreeAugment δ ζ) B H :=
  ⟨I.constraints.map (fun c => c.degreeAugment δ ζ)⟩

/-- Actual assignment weight in the augmented instance splits into its original
weight and one root factor per occurrence. -/
theorem eval_degreeAugment (I : Instance L B H) (δ : ℕ) (ζ : K)
    (a : B → D × Fin δ) (b : H → D × Fin δ) :
    (I.degreeAugment δ ζ).eval a b =
      I.eval (fun v => (a v).1) (fun v => (b v).1) *
        (I.occurrences.map (fun v => ζ ^ (Sum.elim a b v).2.val)).prod := by
  have hsplit : (fun v : B ⊕ H => (Sum.elim a b v).1) =
      Sum.elim (fun v => (a v).1) (fun v => (b v).1) := by
    funext v
    cases v <;> rfl
  cases I with
  | mk cs =>
    induction cs with
    | nil => simp [degreeAugment, eval, occurrences]
    | cons c cs ih =>
      simp only [degreeAugment, eval, List.map_cons, List.prod_cons,
        Constraint.degreeAugment, Constraint.eval, Language.degreeAugment,
        Function.comp_def, occurrences, List.flatMap_cons,
        List.map_append, List.prod_append, List.map_ofFn, List.prod_ofFn] at ih ⊢
      rw [ih]
      have hc : L.value c.symbol (fun t => (Sum.elim a b (c.scope t)).1) =
          L.value c.symbol (fun t => Sum.elim (fun v => (a v).1)
            (fun v => (b v).1) (c.scope t)) := by rw [← hsplit]
      rw [hc]
      exact mul_mul_mul_comm _ _ _ _

/-- The cyclic contribution of an assignment to all variables. -/
def cyclicWeight (I : Instance L B H) (ζ : K) {δ : ℕ}
    (θ : (B ⊕ H) → Fin δ) : K :=
  (I.occurrences.map (fun v => ζ ^ (θ v).val)).prod

/-- The two coordinates of an augmented hidden assignment are independent. -/
theorem partition_degreeAugment [Fintype D] [Fintype H] [DecidableEq H]
    (I : Instance L B H) (δ : ℕ) (ζ : K) (a : B → D) (s : B → Fin δ) :
    (I.degreeAugment δ ζ).partition (fun v => (a v, s v)) =
      I.partition a * ∑ t : H → Fin δ, I.cyclicWeight ζ (Sum.elim s t) := by
  have hweight (b : H → D × Fin δ) :
      (I.degreeAugment δ ζ).eval (fun v => (a v, s v)) b =
        I.eval a (fun v => (b v).1) *
          I.cyclicWeight ζ (Sum.elim s (fun v => (b v).2)) := by
    rw [eval_degreeAugment]
    congr 1
    unfold cyclicWeight
    congr 2
    funext v
    cases v <;> rfl
  simp only [partition, hweight]
  rw [Finset.sum_mul_sum]
  exact (Equiv.arrowProdEquivProdArrow H (fun _ => D) (fun _ => Fin δ)).sum_comp
    (fun b => I.eval a b.1 * I.cyclicWeight ζ (Sum.elim s b.2)) |>.trans
      (Fintype.sum_prod_type _)

/-- Summing the augmented partitions over all cyclic boundary pins sums over
all cyclic coordinates, including the hidden variables. -/
theorem sum_pins_degreeAugment [Fintype D] [Fintype B] [Fintype H]
    [DecidableEq B] [DecidableEq H]
    (I : Instance L B H) (δ : ℕ) (ζ : K) (a : B → D) :
    (∑ s : B → Fin δ, (I.degreeAugment δ ζ).partition (fun v => (a v, s v))) =
      I.partition a * ∑ θ : (B ⊕ H) → Fin δ, I.cyclicWeight ζ θ := by
  simp only [partition_degreeAugment, ← Finset.mul_sum]
  congr 1
  exact (((Equiv.sumArrowEquivProdArrow B H (Fin δ)).symm.sum_comp
    (I.cyclicWeight ζ)).symm.trans (Fintype.sum_prod_type _)).symm

end Instance

namespace Instance

variable {D K ι B H : Type} [Field K] {L : Language D K ι}
variable [Fintype B] [Fintype H] [DecidableEq B] [DecidableEq H]

/-- Cyclic orthogonality applied separately to every actual variable degree. -/
theorem sum_cyclicWeight (I : Instance L B H) {δ : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ δ) :
    (∑ θ : (B ⊕ H) → Fin δ, I.cyclicWeight ζ θ) =
      if ∀ v, δ ∣ I.occurrenceDegree v then
        (δ : K) ^ (Fintype.card B + Fintype.card H) else 0 := by
  classical
  simp only [cyclicWeight, auxiliary_weight_by_degree]
  rw [← Fintype.prod_sum (fun v (t : Fin δ) => ζ ^ (t.val * I.occurrenceDegree v))]
  simp_rw [cyclic_degree_sum hζ]
  rw [Fintype.prod_ite_zero]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_sum]

/-- The paper's degree-filter identity (equations degree-filter-H/G), with
literal finite instances, actual occurrence degrees, and all cyclic label pins.
No character-comparison or equality-decision oracle is used in this theorem. -/
theorem degree_filter_identity [Fintype D] (I : Instance L B H)
    {δ : ℕ} {ζ : K} (hζ : IsPrimitiveRoot ζ δ) (a : B → D) :
    (∑ s : B → Fin δ, (I.degreeAugment δ ζ).partition (fun v => (a v, s v))) =
      if ∀ v, δ ∣ I.occurrenceDegree v then
        (δ : K) ^ (Fintype.card B + Fintype.card H) * I.partition a else 0 := by
  rw [sum_pins_degreeAugment, sum_cyclicWeight I hζ]
  split_ifs <;> simp [mul_comm]

end Instance

end ComplexCSP
