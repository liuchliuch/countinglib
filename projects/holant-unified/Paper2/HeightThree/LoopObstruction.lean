import Paper2.HeightThree.EOOutputs
import Paper2.HeightThree.LoopWitness

namespace Paper2.HeightThree
open Certificates.Q6

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma eoWords_complete (x : Fin 4 → Bool) (hx : weight x = 2) : ∃ e, eoWords e = x := by
  revert x
  decide +kernel

lemma complementCoord_involutive (i : Fin 20) : complementCoord (complementCoord i) = i := by
  fin_cases i <;> rfl

variable {K : Type} [CommRing K] [IsDomain K]

lemma oneComplementPair_nonzero {q : Fin 20 → K} (hn : q ≠ 0) (h : OneComplementPair q) :
    ∃ i, q i ≠ 0 ∧ ∀ j, q j ≠ 0 → j = i ∨ j = complementCoord i := by
  obtain ⟨i,hi⟩ := h
  by_cases hqi : q i = 0
  · have hci : q (complementCoord i) ≠ 0 := by
      intro hz
      apply hn
      funext j
      by_cases hj : q j = 0
      · exact hj
      · rcases hi j hj with rfl | rfl
        · exact hqi
        · exact hz
    refine ⟨complementCoord i,hci,?_⟩
    intro j hj
    rcases hi j hj with hji | hji
    · exact Or.inr (hji.trans (complementCoord_involutive i).symm)
    · exact Or.inl hji
  · exact ⟨i,hqi,hi⟩

/-- Two possible EO entries cannot be a nonsingular weighted matching product,
whose actual truth-table support has cardinality four. -/
lemma not_product_of_two_entries (f : Signature K 4)
    (hEO : ∀ x, weight x ≠ 2 → f x = 0) (e₀ : Fin 6)
    (hs : ∀ e, e ≠ e₀ → e ≠ entryComplement e₀ → f (eoWords e) = 0) :
    ¬ WeightedMatching.IsProduct f := by
  classical
  have hsub : Matching.support f ⊆ {eoWords e₀,eoWords (entryComplement e₀)} := by
    intro x hx
    have hn : f x ≠ 0 := (Finset.mem_filter.mp hx).2
    have hw : weight x = 2 := by by_contra h; exact hn (hEO x h)
    obtain ⟨e,rfl⟩ := eoWords_complete x hw
    by_cases he : e = e₀
    · exact Finset.mem_insert.mpr (Or.inl (congrArg eoWords he))
    by_cases he' : e = entryComplement e₀
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr (congrArg eoWords he')))
    exact False.elim (hn (hs e he he'))
  have hc := Finset.card_le_card hsub
  have hpair : ({eoWords e₀,eoWords (entryComplement e₀)} : Finset (Fin 4 → Bool)).card ≤ 2 :=
    by simpa using Finset.card_insert_le (eoWords e₀) {eoWords (entryComplement e₀)}
  rintro ⟨P,p,q,c,hn,heq⟩
  have hcount : P.count = 2 := by have hh := Matching.pair_count P; omega
  rw [heq,WeightedMatching.card_support_product P p q c hn,hcount] at hc
  omega

lemma revealingLoop_nonmatching (a b : K) (q : Fin 20 → K)
    (hq : q ≠ 0) (hp : OneComplementPair q) :
    ∃ i : Fin 15, loopSignature (coordinateMountain a b q) i ≠ 0 ∧
      ¬ WeightedMatching.IsProduct (loopSignature (coordinateMountain a b q) i) := by
  obtain ⟨k,hk,hpair⟩ := oneComplementPair_nonzero hq hp
  refine ⟨(revealingLoop k).1,?_,?_⟩
  · intro hz
    have he := congrFun hz (eoWords (revealingLoop k).2)
    rw [loopSignature_array,revealingLoop_value q k hpair] at he
    exact hk he
  · apply not_product_of_two_entries _ (loopSignature_zero_off_two a b q (revealingLoop k).1)
      (revealingLoop k).2
    intro e he he'
    rw [loopSignature_array]
    exact revealingLoop_zero q k hpair e ⟨he,he'⟩

lemma coefficient_zero (m : ℕ) : coefficient (0 : Fin 20 → K) m = 0 := by
  unfold coefficient
  split <;> rfl

lemma twoCopyArray_zero (t : K) (s : CardSpec) (e : Fin 6) :
    twoCopyArray (0 : Fin 20 → K) t s e = (if e = 0 ∨ e = 5 then t else 0) := by
  simp only [twoCopyArray,coefficient_zero,zero_mul,Finset.sum_const_zero,add_zero]

lemma zero_center_card_nonmatching (a b : K) (hab : a*b ≠ 0)
    (s : CardSpec) (hs : RawValidCardSpec s) :
    (cardNetwork s hs (coordinateMountain a b (0 : Fin 20 → K))).denote ≠ 0 ∧
    ¬ WeightedMatching.IsProduct (cardNetwork s hs (coordinateMountain a b (0 : Fin 20 → K))).denote := by
  constructor
  · intro hz
    have he := congrFun hz (eoWords 0)
    rw [cardNetwork_array,twoCopyArray_zero] at he
    exact hab (by simpa using he)
  · apply not_product_of_two_entries _ (cardNetwork_zero_off_two a b 0 s hs) 0
    intro e he he'
    rw [cardNetwork_array,twoCopyArray_zero,if_neg]
    exact not_or.mpr ⟨he,he'⟩

end Paper2.HeightThree
