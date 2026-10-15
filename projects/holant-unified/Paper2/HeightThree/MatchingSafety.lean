import Paper2.WeightedMatching
import Paper2.Certificates.Q6Entry

/-! The necessary finite-array safety equations follow from the actual
weighted matching-product class on four ordered ports. -/
namespace Paper2.HeightThree
open Certificates.Q6
open scoped BigOperators

variable {K : Type*} [CommRing K] [IsDomain K]

lemma transversal_complement {n : ℕ} (P : WeightedMatching.Pairing n)
    (x : Fin n → Bool) :
    WeightedMatching.Transversal P (fun i => !(x i)) ↔ WeightedMatching.Transversal P x := by
  unfold WeightedMatching.Transversal
  constructor <;> intro h j <;> have hj := h j
  all_goals cases ha : x (P.ports (j,false)) <;> cases hb : x (P.ports (j,true)) <;> simp_all

lemma product_complement_nonzero {n : ℕ} (P : WeightedMatching.Pairing n)
    (p q : Fin P.count → K) (c : K) (hc : c * ∏ j, p j * q j ≠ 0)
    (x : Fin n → Bool) :
    WeightedMatching.product P p q c (fun i => !(x i)) ≠ 0 ↔
      WeightedMatching.product P p q c x ≠ 0 := by
  rw [WeightedMatching.product_ne_zero P p q c hc,
    WeightedMatching.product_ne_zero P p q c hc]
  exact transversal_complement P x

lemma product_complement_value {n : ℕ} (P : WeightedMatching.Pairing n)
    (p q : Fin P.count → K) (c : K) (x : Fin n → Bool)
    (hx : WeightedMatching.Transversal P x) :
    WeightedMatching.product P p q c x *
      WeightedMatching.product P p q c (fun i => !(x i)) = c^2 * ∏ j, p j * q j := by
  unfold WeightedMatching.product
  rw [mul_mul_mul_comm,← Finset.prod_mul_distrib,pow_two]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  change WeightedMatching.binary (p j) (q j) (x (P.ports (j,false))) (x (P.ports (j,true))) *
    WeightedMatching.binary (p j) (q j) (!(x (P.ports (j,false)))) (!(x (P.ports (j,true)))) = _
  rw [hx j]
  cases x (P.ports (j,false)) <;> simp [WeightedMatching.binary,mul_comm]

lemma eoWords_complement (e : Fin 6) :
    eoWords (entryComplement e) = fun j => !(eoWords e j) := by
  funext j
  fin_cases e <;> fin_cases j <;> rfl

lemma eoWords_injective : Function.Injective eoWords := by
  intro i j h
  apply entrySet_injective
  unfold entrySet
  rw [h]

/-- A full weighted matching product has only four nonzero truth-table entries;
therefore at least one of the six EO entries vanishes. -/
lemma product_quaternary_zero (P : WeightedMatching.Pairing 4)
    (p q : Fin P.count → K) (c : K) (hc : c * ∏ j, p j * q j ≠ 0) :
    ∃ e : Fin 6, WeightedMatching.product P p q c (eoWords e) = 0 := by
  classical
  by_contra h
  push_neg at h
  have hcount : P.count = 2 := by have hp := Matching.pair_count P; omega
  have hsub : Finset.univ.image eoWords ⊆ Matching.support (WeightedMatching.product P p q c) := by
    intro x hx
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h e⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ eoWords_injective,
    WeightedMatching.card_support_product P p q c hc,hcount] at hcard
  norm_num at hcard

theorem product_necessary_safe (P : WeightedMatching.Pairing 4)
    (p q : Fin P.count → K) (c : K) (hc : c * ∏ j, p j * q j ≠ 0) :
    NecessarySafe (fun e => WeightedMatching.product P p q c (eoWords e)) := by
  apply SymmetricSafe.necessary
  refine ⟨?_,product_quaternary_zero P p q c hc,?_⟩
  · intro e
    dsimp only
    rw [eoWords_complement]
    exact not_iff_not.mp (product_complement_nonzero P p q c hc (eoWords e)).symm
  · intro i j
    by_cases hi : WeightedMatching.product P p q c (eoWords i) *
        WeightedMatching.product P p q c (eoWords (entryComplement i)) = 0
    · exact Or.inl hi
    by_cases hj : WeightedMatching.product P p q c (eoWords j) *
        WeightedMatching.product P p q c (eoWords (entryComplement j)) = 0
    · exact Or.inr (Or.inl hj)
    apply Or.inr ∘ Or.inr
    have hx : WeightedMatching.Transversal P (eoWords i) :=
      (WeightedMatching.product_ne_zero P p q c hc _).mp (mul_ne_zero_iff.mp hi).1
    have hy : WeightedMatching.Transversal P (eoWords j) :=
      (WeightedMatching.product_ne_zero P p q c hc _).mp (mul_ne_zero_iff.mp hj).1
    dsimp only
    rw [eoWords_complement,eoWords_complement,
      product_complement_value P p q c _ hx,product_complement_value P p q c _ hy]

/-- Source-exact B×⁰ membership implies the certificate predicate. -/
theorem matching_or_zero_necessary_safe (f : Signature K 4)
    (h : f = 0 ∨ WeightedMatching.IsProduct f) : NecessarySafe (fun e => f (eoWords e)) := by
  rcases h with rfl | ⟨P,p,q,c,hc,rfl⟩
  · constructor <;> simp
  · exact product_necessary_safe P p q c hc

end Paper2.HeightThree
