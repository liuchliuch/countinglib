import Paper2.HeightThree.CardSum
import Paper2.Certificates.Q6CardComplement

namespace Paper2.HeightThree
open Certificates.Q6

lemma selected_card (a b : Port) (h : a ≠ b) (x y : Bool) :
    (selected a b x y).card = x.toNat + y.toNat := by
  cases x <;> cases y <;> simp [selected,h]

lemma selected_disjoint (a b : Port) (x y : Bool) (T : PortSet)
    (hT : T ⊆ Finset.univ \ {a,b}) : Disjoint (selected a b x y) T := by
  have hh := subset_not_external a b T hT
  cases x <;> cases y <;> simp [selected,Finset.disjoint_left,hh.1,hh.2]

lemma selected_union_card (a b : Port) (h : a ≠ b) (x y : Bool)
    (T : PortSet) (hT : T ⊆ Finset.univ \ {a,b}) :
    (selected a b x y ∪ T).card = x.toNat + y.toNat + T.card := by
  rw [Finset.card_union_of_disjoint (selected_disjoint a b x y T hT),selected_card a b h]

lemma rightInterior_card (s : CardSpec) (hs : RawValidCardSpec s) :
    (internalRight s).card = 4 := by
  rw [internalRight,Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_pair hs.2.1]
  rfl

lemma sourceSetsAt_cards (s : CardSpec) (hs : RawValidCardSpec s)
    (x : Fin 4 → Bool) (T : PortSet) (hT : T ⊆ internalLeft s) :
    (sourceSetsAt s x T).1.card = (x 0).toNat + (x 1).toNat + T.card ∧
    (sourceSetsAt s x T).2.card = (x 2).toNat + (x 3).toNat + (4-T.card) := by
  constructor
  · exact selected_union_card _ _ hs.1 _ _ T hT
  · have him : T.image s.wiring ⊆ internalRight s := by
      rw [← hs.2.2.2]
      exact Finset.image_subset_image hT
    change (selected s.right0 s.right1 (x 2) (x 3) ∪ (internalRight s \ T.image s.wiring)).card = _
    rw [selected_union_card s.right0 s.right1 hs.2.1 (x 2) (x 3)
      (internalRight s \ T.image s.wiring) Finset.sdiff_subset,
      Finset.card_sdiff_of_subset him,rightInterior_card s hs,
      Finset.card_image_iff.mpr hs.2.2.1.1.injOn]

lemma internal_subset_card_le (s : CardSpec) (hs : RawValidCardSpec s)
    (T : PortSet) (hT : T ⊆ internalLeft s) : T.card ≤ 4 := by
  exact (Finset.card_le_card hT).trans_eq (internalLeft_card s hs)

lemma internal_subset_card_eq_four (s : CardSpec) (hs : RawValidCardSpec s)
    (T : PortSet) (hT : T ⊆ internalLeft s) : T.card = 4 ↔ T = internalLeft s := by
  constructor
  · intro hc
    exact Finset.eq_of_subset_of_card_le hT (by rw [internalLeft_card s hs,hc])
  · rintro rfl
    exact internalLeft_card s hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma subsetWord_constant_iff (S : PortSet) (b : Bool) :
    subsetWord S = (fun _ => b) ↔ S.card = (if b then 6 else 0) := by
  revert S b
  decide +kernel

variable {K : Type} [CommSemiring K]

lemma coordinateMountain_subset (a b : K) (q : Fin 20 → K) (S : PortSet) :
    coordinateMountain a b q (subsetWord S) =
      (if S.card = 0 then a else 0) + (if S.card = 6 then b else 0) + coefficient q (mask S) := by
  simp only [coordinateMountain,subsetWord_constant_iff,occupied_subsetWord,Bool.false_eq_true,ite_false,ite_true]

end Paper2.HeightThree
