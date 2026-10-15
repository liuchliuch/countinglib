import Paper2.WeightedMatching

/-! Lightweight pure matching facts, extracted from HeightThree.MatchingSafety
without importing the unrelated finite Q6 atlas. Every statement is freshly
kernel checked here for use in the genuine Gram network argument. -/
namespace Paper2.RelativeEO.MatchingComplement
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


theorem equal_supported_complement_products {n : ℕ} {f : Signature K n}
    (hf : WeightedMatching.IsProduct f) (x y : Fin n → Bool)
    (hx : f x ≠ 0) (hy : f y ≠ 0) :
    f x * f (fun i => !(x i)) = f y * f (fun i => !(y i)) := by
  obtain ⟨P,p,q,c,hc,rfl⟩ := hf
  rw [product_complement_value P p q c x
    ((WeightedMatching.product_ne_zero P p q c hc x).mp hx),
    product_complement_value P p q c y
    ((WeightedMatching.product_ne_zero P p q c hc y).mp hy)]

theorem zero_of_unequal_complement_products {n : ℕ} {f : Signature K n}
    (hf : WeightedMatching.IsProduct f) (x y : Fin n → Bool)
    (hne : f x * f (fun i => !(x i)) ≠ f y * f (fun i => !(y i))) :
    f x = 0 ∨ f y = 0 := by
  by_contra h
  push_neg at h
  exact hne (equal_supported_complement_products hf x y h.1 h.2)

theorem support_card {n : ℕ} {f : Signature K n} (hf : WeightedMatching.IsProduct f) :
    (Matching.support f).card = 2 ^ (n / 2) := by
  obtain ⟨P,p,q,c,hc,rfl⟩ := hf
  have hp : P.count = n / 2 := by have := Matching.pair_count P; omega
  rw [WeightedMatching.card_support_product P p q c hc, hp]

theorem quaternary_support_card {f : Signature K 4} (hf : WeightedMatching.IsProduct f) :
    (Matching.support f).card = 4 := by simpa using support_card hf

end Paper2.RelativeEO.MatchingComplement

