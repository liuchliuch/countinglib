import Paper2.HeightOne.Cyclic.MatchingSupport
import Mathlib.Data.Fintype.Pigeonhole

/-! Source zero-pair elimination above four ports. The proof is a direct
pigeonhole argument on the ports outside a putative forced-disequality pair.
It needs only two distinct actual phase contractions and their origin values. -/
namespace Paper2.HeightOne.Cyclic
noncomputable section
open EndpointSelfLoop
variable {K : Type*} [Field K] {ι : Type} [Fintype ι]

lemma extendBits_remaining (a b : ι) (hab : a ≠ b) (x : Remaining a b → Bool)
    (u v : Bool) (i : Remaining a b) : extendBits a b hab x u v i.val = x i := by
  classical
  simp only [extendBits, splitPorts, dif_neg i.property.1, dif_neg i.property.2, Equiv.coe_fn_mk, Sum.elim_inl]
  exact congrArg x (Subtype.ext rfl)

/-- A zero pair means the actual tensor support forces opposite bits there. -/
def ZeroPair (f : Tensor K ι) (a b : ι) : Prop :=
  a ≠ b ∧ ∀ x, f x ≠ 0 → x a ≠ x b

lemma zeroPair_iff_two_cards_zero (f : Tensor K ι) (a b : ι) (hab : a ≠ b)
    (s t : K) (hst : s ≠ t) :
    ZeroPair f a b ↔ plusContraction a b hab s f = 0 ∧ plusContraction a b hab t f = 0 := by
  classical
  constructor
  · intro hz
    have hsame (x : Remaining a b → Bool) (v : Bool) : f (extendBits a b hab x v v) = 0 := by
      by_contra h
      apply hz.2 _ h
      simp [extendBits, splitPorts, hab, Ne.symm hab]
    constructor <;> funext x <;> simp [plusContraction_apply, hsame]
  · rintro ⟨hs, ht⟩
    refine ⟨hab, ?_⟩
    intro x hx heq
    have hzero := affine_two_roots hst
      (show f (extendBits a b hab (restrict a b x) false false) -
        s * f (extendBits a b hab (restrict a b x) true true) = 0 by
          simpa only [plusContraction_apply, Pi.zero_apply] using congrFun hs (restrict a b x))
      (show f (extendBits a b hab (restrict a b x) false false) -
        t * f (extendBits a b hab (restrict a b x) true true) = 0 by
          simpa only [plusContraction_apply, Pi.zero_apply] using congrFun ht (restrict a b x))
    exact (endpoint_pair_nonzero a b hab f x hx heq).elim (fun h => h hzero.1) (fun h => h hzero.2)

/-- A supported word has equal bits on some pair outside any two fixed ports
when at least five ports exist. A nonzero contraction at that outside pair
cannot have a nonzero origin if the fixed pair forces disequality. -/
theorem no_zeroPair_of_origin_cards (f : Tensor K ι) (hf : f ≠ 0)
    (hn : 5 ≤ Fintype.card ι) (s t : K) (hst : s ≠ t)
    (hcards : ∀ a b : ι, ∀ hab : a ≠ b,
      (plusContraction a b hab s f ≠ 0 → plusContraction a b hab s f (fun _ => false) ≠ 0) ∧
      (plusContraction a b hab t f ≠ 0 → plusContraction a b hab t f (fun _ => false) ≠ 0)) :
    ∀ u v, ¬ ZeroPair f u v := by
  classical
  intro u v huv
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (funext h)
  have hrem := remaining_card u v huv.1
  obtain ⟨a, b, hab, hbits⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun k : Remaining u v => w k.val) (by simp only [Fintype.card_bool]; omega)
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  have hend := endpoint_pair_nonzero a.val b.val hab' f w hw hbits
  have hzero (q : Bool) : f (extendBits a.val b.val hab' (fun _ => false) q q) = 0 := by
    by_contra h
    apply huv.2 _ h
    have hu : extendBits a.val b.val hab' (fun _ => false) q q u = false :=
      extendBits_remaining _ _ _ _ _ _ ⟨u, Ne.symm a.property.1, Ne.symm b.property.1⟩
    have hv : extendBits a.val b.val hab' (fun _ => false) q q v = false :=
      extendBits_remaining _ _ _ _ _ _ ⟨v, Ne.symm a.property.2, Ne.symm b.property.2⟩
    exact hu.trans hv.symm
  have hz (r : K) : plusContraction a.val b.val hab' r f (fun _ => false) = 0 := by
    simp [plusContraction_apply, hzero]
  rcases affine_survives_one_of_two hst hend with hs | ht
  · apply (hcards a.val b.val hab').1
    · intro h
      exact hs (by simpa only [plusContraction_apply, Pi.zero_apply] using congrFun h (restrict a.val b.val w))
    · exact hz s
  · apply (hcards a.val b.val hab').2
    · intro h
      exact ht (by simpa only [plusContraction_apply, Pi.zero_apply] using congrFun h (restrict a.val b.val w))
    · exact hz t

/-- In particular every original port pair has a surviving phase contraction. -/
theorem every_pair_visible_of_origin_cards (f : Tensor K ι) (hf : f ≠ 0)
    (hn : 5 ≤ Fintype.card ι) (s t : K) (hst : s ≠ t)
    (hcards : ∀ a b : ι, ∀ hab : a ≠ b,
      (plusContraction a b hab s f ≠ 0 → plusContraction a b hab s f (fun _ => false) ≠ 0) ∧
      (plusContraction a b hab t f ≠ 0 → plusContraction a b hab t f (fun _ => false) ≠ 0)) :
    ∀ a b (hab : a ≠ b), plusContraction a b hab s f ≠ 0 ∨ plusContraction a b hab t f ≠ 0 := by
  intro a b hab
  by_contra h
  push Not at h
  exact no_zeroPair_of_origin_cards f hf hn s t hst hcards a b
    ((zeroPair_iff_two_cards_zero f a b hab s t hst).mpr h)

end
end Paper2.HeightOne.Cyclic
