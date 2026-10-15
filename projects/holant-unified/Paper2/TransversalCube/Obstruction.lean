import Paper2.TransversalCube.Table

namespace Paper2.TransversalCube
open scoped BigOperators
open Tractable
noncomputable section

/-- The six indicated words are exactly the entire central layer at arity four. -/
lemma six_iff_weight_two (x : Fin 4 → Bool) :
    (x = ![false,false,true,true] ∨ x = ![true,true,false,false] ∨
      (x 1 = !(x 0) ∧ x 3 = !(x 2))) ↔ weight x = 2 := by
  revert x
  decide +kernel

lemma six_support_card {K : Type*} [CommRing K] [IsDomain K] (f : Signature K 4)
    (hf : ∀ x, f x ≠ 0 ↔ weight x = 2) : (Matching.support f).card = 6 := by
  classical
  have he : Matching.support f = Finset.univ.filter (fun x : Fin 4 → Bool => weight x = 2) := by
    ext x; simp [Matching.support,hf]
  rw [he]
  decide +kernel

lemma six_not_isProduct {K : Type*} [CommRing K] [IsDomain K]
    (f : Signature K 4) (hf : ∀ x, f x ≠ 0 ↔ weight x = 2) :
    ¬ WeightedMatching.IsProduct f := by
  rintro ⟨P,p,q,c,hnz,heq⟩
  have hc := WeightedMatching.card_support_product P p q c hnz
  have hcount := Matching.pair_count P
  have hcount2 : P.count = 2 := by omega
  rw [← heq,six_support_card f hf,hcount2] at hc
  norm_num at hc

lemma six_isEO (f : Signature AlgebraicComplex 4)
    (hf : ∀ x, f x ≠ 0 ↔ weight x = 2) : Tractable.IsEO ⟨4,f⟩ := by
  refine ⟨⟨2,rfl⟩,?_⟩
  intro x hx
  change 2 * weight x ≠ 4 at hx
  by_contra hn
  have := (hf x).1 hn
  omega

/-- Both source signs fail directly, before any A/P restriction test is needed. -/
lemma six_not_eoTract (f : Signature AlgebraicComplex 4)
    (hf : ∀ x, f x ≠ 0 ↔ weight x = 2) :
    ¬ Tractable.EOTract {⟨4,f⟩} := by
  rintro ⟨_,_,sign,C,hs,_⟩
  have hmem : (⟨4,f⟩ : AnySignature AlgebraicComplex) ∈ ({⟨4,f⟩} : SignatureFamily AlgebraicComplex) :=
    Set.mem_singleton _
  have h1100 : f ![true,true,false,false] ≠ 0 := (hf _).2 (by decide +kernel)
  have h1010 : f ![true,false,true,false] ≠ 0 := (hf _).2 (by decide +kernel)
  have h0110 : f ![false,true,true,false] ≠ 0 := (hf _).2 (by decide +kernel)
  have h0011 : f ![false,false,true,true] ≠ 0 := (hf _).2 (by decide +kernel)
  have h0101 : f ![false,true,false,true] ≠ 0 := (hf _).2 (by decide +kernel)
  have h1001 : f ![true,false,false,true] ≠ 0 := (hf _).2 (by decide +kernel)
  cases sign
  · have hh := hs ⟨4,f⟩ hmem _ _ _ h1100 h1010 h0110
    have he : Tractable.tripleXor ![true,true,false,false] ![true,false,true,false]
        ![false,true,true,false] = (fun _ => false) := by decide +kernel
    rw [he] at hh
    rcases hh with hh | hh
    · have := (hf _).1 hh
      simp at this
    · norm_num [Tractable.EOSign.value,charge] at hh
  · have hh := hs ⟨4,f⟩ hmem _ _ _ h0011 h0101 h1001
    have he : Tractable.tripleXor ![false,false,true,true] ![false,true,false,true]
        ![true,false,false,true] = (fun _ => true) := by decide +kernel
    rw [he] at hh
    rcases hh with hh | hh
    · have := (hf _).1 hh
      simp at this
    · norm_num [Tractable.EOSign.value,charge] at hh

variable {K : Type*} [CommRing K] [IsDomain K] {m : ℕ}

lemma contract_weight_two (hm : 2 ≤ m) (a b c : K) (p q : Fin (m+1) → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : c * ∏ j, p j * q j ≠ 0)
    (x : Fin 4 → Bool) : contract a b c p q x ≠ 0 ↔ weight x = 2 :=
  (contract_support hm a b c p q ha hb h x).trans (six_iff_weight_two x)

/-- The four central/central coefficients have nonzero product, so no
cancellation remains hidden in the network's finite sum. -/
lemma contract_four_nonzero (hm : 2 ≤ m) (a b c : K) (p q : Fin (m+1) → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : c * ∏ j, p j * q j ≠ 0) :
    contract a b c p q ![false,true,false,true] *
    contract a b c p q ![false,true,true,false] *
    contract a b c p q ![true,false,false,true] *
    contract a b c p q ![true,false,true,false] ≠ 0 := by
  repeat apply mul_ne_zero
  all_goals exact (contract_weight_two hm a b c p q ha hb h _).2 (by decide +kernel)

end
end Paper2.TransversalCube
