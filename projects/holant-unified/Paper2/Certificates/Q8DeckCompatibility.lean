import Paper2.Certificates.Q8ActualDeckCore
import Paper2.HighHeightReconstruction.SpliceSupport

/-! Commuting actual double contractions force equality of the atlas splice
maps. This is a tensor-support theorem, independent of the finite search. -/
namespace Paper2.Certificates.Q8.Atlas
open CommonPhase

lemma Matching.extend_on {d : PairIndex} (M : Matching d) (v : Remaining d) :
    M.extend v.val = (M.mate v).val := by
  rw [Matching.extend,dif_pos v.property]

lemma Matching.extend_off {d : PairIndex} (M : Matching d) (v : Port)
    (h : v = (deleted d).1 ∨ v = (deleted d).2) : M.extend v = v := by
  have hh : ¬(v ≠ (deleted d).1 ∧ v ≠ (deleted d).2) := by aesop
  rw [Matching.extend,dif_neg hh]

lemma Matching.extend_remaining {d : PairIndex} (M : Matching d) (v : Port)
    (hv : v ≠ (deleted d).1 ∧ v ≠ (deleted d).2) :
    M.extend v ≠ (deleted d).1 ∧ M.extend v ≠ (deleted d).2 := by
  rw [show v = (⟨v,hv⟩ : Remaining d).val from rfl,M.extend_on]
  exact (M.mate ⟨v,hv⟩).property

lemma Matching.extend_no_fixed {d : PairIndex} (M : Matching d) (v : Port)
    (hv : v ≠ (deleted d).1 ∧ v ≠ (deleted d).2) : M.extend v ≠ v := by
  intro h
  rw [show v = (⟨v,hv⟩ : Remaining d).val from rfl,M.extend_on] at h
  exact M.no_fixed ⟨v,hv⟩ (Subtype.ext h)

lemma Matching.extend_involutive {d : PairIndex} (M : Matching d) : Function.Involutive M.extend := by
  intro v
  by_cases hv : v ≠ (deleted d).1 ∧ v ≠ (deleted d).2
  · rw [show v = (⟨v,hv⟩ : Remaining d).val from rfl,M.extend_on,M.extend_on]
    exact congrArg Subtype.val (M.involutive ⟨v,hv⟩)
  · have hh : v = (deleted d).1 ∨ v = (deleted d).2 := by
      by_cases hp : v = (deleted d).1
      · exact Or.inl hp
      · exact Or.inr (not_not.mp (fun hq => hv ⟨hp,hq⟩))
    rw [M.extend_off v hh,M.extend_off v hh]

lemma involution_value_eq {α : Type*} (m : α → α) (hm : Function.Involutive m) (a b : α) :
    m a = b ↔ m b = a := by
  constructor <;> intro h
  · have hh := congrArg m h
    rw [hm a] at hh
    exact hh.symm
  · have hh := congrArg m h
    rw [hm b] at hh
    exact hh.symm

lemma Matching.splice_fixed {d : PairIndex} (M : Matching d) (e : PairIndex) (v : Port)
    (h : (v = (deleted d).1 ∨ v = (deleted d).2) ∨
      (v = (deleted e).1 ∨ v = (deleted e).2)) : spliceMate M.extend e v = v := by
  by_cases he : v = (deleted e).1 ∨ v = (deleted e).2
  · simp only [spliceMate,he,ite_true]
  · have hd := h.resolve_right he
    have hm := M.extend_off v hd
    have he₁ : v ≠ (deleted e).1 := fun h => he (Or.inl h)
    have he₂ : v ≠ (deleted e).2 := fun h => he (Or.inr h)
    simp only [spliceMate,he,ite_false,hm,he₁,he₂,false_or]

/-- Surviving ports remain paired with a distinct surviving port after deletion. -/
lemma Matching.splice_remaining {d e : PairIndex} (M : Matching d)
    (hde : DisjointDeleted d e) (v : Port)
    (hd : v ≠ (deleted d).1 ∧ v ≠ (deleted d).2)
    (he : v ≠ (deleted e).1 ∧ v ≠ (deleted e).2) :
    let w := spliceMate M.extend e v
    w ≠ v ∧ (w ≠ (deleted d).1 ∧ w ≠ (deleted d).2) ∧
      (w ≠ (deleted e).1 ∧ w ≠ (deleted e).2) := by
  have hp : (deleted e).1 ≠ (deleted d).1 ∧ (deleted e).1 ≠ (deleted d).2 :=
    ⟨hde.1.symm,hde.2.2.1.symm⟩
  have hq : (deleted e).2 ≠ (deleted d).1 ∧ (deleted e).2 ≠ (deleted d).2 :=
    ⟨hde.2.1.symm,hde.2.2.2.symm⟩
  have hinj := M.extend_involutive.injective
  have hv : ¬(v = (deleted e).1 ∨ v = (deleted e).2) := not_or.mpr he
  dsimp only
  unfold spliceMate
  rw [if_neg hv]
  by_cases ha : M.extend v = (deleted e).1
  · rw [if_pos ha]
    refine ⟨?_,M.extend_remaining _ hq,?_,M.extend_no_fixed _ hq⟩
    · intro h
      have hh := (involution_value_eq _ M.extend_involutive _ _).mp h
      rw [ha] at hh
      exact deleted_distinct e hh
    · intro h
      exact he.2 (hinj (ha.trans h.symm))
  · rw [if_neg ha]
    by_cases hb : M.extend v = (deleted e).2
    · rw [if_pos hb]
      refine ⟨?_,M.extend_remaining _ hp,M.extend_no_fixed _ hp,?_⟩
      · intro h
        have hh := (involution_value_eq _ M.extend_involutive _ _).mp h
        rw [hb] at hh
        exact (deleted_distinct e) hh.symm
      · intro h
        exact he.1 (hinj (hb.trans h.symm))
    · rw [if_neg hb]
      exact ⟨M.extend_no_fixed v hd,M.extend_remaining v hd,ha,hb⟩

lemma Matching.splice_eq_iff {d : PairIndex} (M : Matching d) (e : PairIndex) (v w : Port)
    (hv : v ≠ (deleted e).1 ∧ v ≠ (deleted e).2)
    (hw : w ≠ (deleted e).1 ∧ w ≠ (deleted e).2) :
    spliceMate M.extend e v = w ↔
      M.extend v = w ∨
      (M.extend v = (deleted e).1 ∧ M.extend w = (deleted e).2) ∨
      (M.extend v = (deleted e).2 ∧ M.extend w = (deleted e).1) := by
  have hv' := not_or.mpr hv
  unfold spliceMate
  rw [if_neg hv']
  by_cases ha : M.extend v = (deleted e).1
  · have hb : M.extend v ≠ (deleted e).2 := by rw [ha]; exact deleted_distinct e
    have hvw : M.extend v ≠ w := by rw [ha]; exact hw.1.symm
    simpa [ha,deleted_distinct e,hw.1.symm] using
      involution_value_eq _ M.extend_involutive (deleted e).2 w
  · by_cases hb : M.extend v = (deleted e).2
    · have hvw : M.extend v ≠ w := by rw [hb]; exact hw.2.symm
      simpa [hb,(deleted_distinct e).symm,hw.2.symm] using
        involution_value_eq _ M.extend_involutive (deleted e).1 w
    · simp only [ha,hb,ite_false,false_and,or_false]

/-- The atlas edge relation is exactly the forced-opposite relation of the
actual residual two-term native-X contraction. -/
lemma indexed_splice_forces_iff
    (P : (r : PortPair Port) → XMatching (EndpointSelfLoop.Remaining r.first r.second))
    (d e : PairIndex) (hde : DisjointDeleted d e) (v w : Port) (hvw : v ≠ w)
    (hvd : v ≠ (deleted d).1 ∧ v ≠ (deleted d).2)
    (hve : v ≠ (deleted e).1 ∧ v ≠ (deleted e).2)
    (hwd : w ≠ (deleted d).1 ∧ w ≠ (deleted d).2)
    (hwe : w ≠ (deleted e).1 ∧ w ≠ (deleted e).2) :
    spliceMate (indexedMatching P d).extend e v = w ↔
      MatchingPropagation.Forces
        (((portPair d).residual (portPair e) hde).pairSum (literal (P (portPair d)) ℂ))
        ⟨v,hvd⟩ ⟨w,hwd⟩ := by
  have h := HighHeightReconstruction.literal_pairSum_forces_iff (P (portPair d))
    ((portPair d).residual (portPair e) hde) (⟨v,hvd⟩ : Remaining d) (⟨w,hwd⟩ : Remaining d)
    (fun he => hvw (congrArg Subtype.val he))
    (fun he => hve.1 (congrArg Subtype.val he))
    (fun he => hve.2 (congrArg Subtype.val he))
    (fun he => hwe.1 (congrArg Subtype.val he))
    (fun he => hwe.2 (congrArg Subtype.val he))
  rw [(indexedMatching P d).splice_eq_iff e v w hve hwe]
  have hv : (indexedMatching P d).extend v =
      (MatchingPropagation.mate (P (portPair d)) (⟨v,hvd⟩ : Remaining d)).val :=
    (indexedMatching P d).extend_on ⟨v,hvd⟩
  have hw : (indexedMatching P d).extend w =
      (MatchingPropagation.mate (P (portPair d)) (⟨w,hwd⟩ : Remaining d)).val :=
    (indexedMatching P d).extend_on ⟨w,hwd⟩
  rw [hv,hw]
  constructor
  · intro he
    apply h.mpr
    rcases he with he | ⟨he,hf⟩ | ⟨he,hf⟩
    · exact Or.inl (Subtype.ext he)
    · exact Or.inr (Or.inl ⟨Subtype.ext he,Subtype.ext hf⟩)
    · exact Or.inr (Or.inr ⟨Subtype.ext he,Subtype.ext hf⟩)
  · intro he
    rcases h.mp he with he | ⟨he,hf⟩ | ⟨he,hf⟩
    · exact Or.inl (congrArg Subtype.val he)
    · exact Or.inr (Or.inl ⟨congrArg Subtype.val he,congrArg Subtype.val hf⟩)
    · exact Or.inr (Or.inr ⟨congrArg Subtype.val he,congrArg Subtype.val hf⟩)

lemma outside_or_deleted (v a b : Port) (h : ¬(v ≠ a ∧ v ≠ b)) : v = a ∨ v = b := by
  by_cases ha : v = a
  · exact Or.inl ha
  · exact Or.inr (not_not.mp (fun hb => h ⟨ha,hb⟩))

/-- Full tensor-to-atlas compatibility: every two actual disjoint self-loops
commute, their nonzero matching scalars cancel, and support identifies mates. -/
theorem matchingDeck_compatible (F : Signature ℂ 8) (lam : PortPair Port → ℂ)
    (P : (r : PortPair Port) → XMatching (EndpointSelfLoop.Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ r, lam r ≠ 0) :
    MatchingFamilyCompatible (indexedMatching P) := by
  intro d e hde
  have hed : DisjointDeleted e d :=
    (show (portPair d).Disjoint (portPair e) from hde).symm
  funext v
  by_cases hvd : v ≠ (deleted d).1 ∧ v ≠ (deleted d).2
  · by_cases hve : v ≠ (deleted e).1 ∧ v ≠ (deleted e).2
    · let w := spliceMate (indexedMatching P d).extend e v
      have hw := (indexedMatching P d).splice_remaining hde v hvd hve
      change w ≠ v ∧ (w ≠ (deleted d).1 ∧ w ≠ (deleted d).2) ∧
        (w ≠ (deleted e).1 ∧ w ≠ (deleted e).2) at hw
      let r : PortPair Port := ⟨v,w,hw.1.symm⟩
      have hdr : (portPair d).Disjoint r :=
        ⟨hvd.1.symm,hw.2.1.1.symm,hvd.2.symm,hw.2.1.2.symm⟩
      have her : (portPair e).Disjoint r :=
        ⟨hve.1.symm,hw.2.2.1.symm,hve.2.symm,hw.2.2.2.symm⟩
      have hleft := (indexed_splice_forces_iff P d e hde v w hw.1.symm hvd hve hw.2.1 hw.2.2).mp rfl
      have hright := (HighHeightReconstruction.double_literal_forces_iff F lam P hd hnz
        (portPair d) (portPair e) r hde hdr her).mp hleft
      exact ((indexed_splice_forces_iff P e d hed v w hw.1.symm hve hvd hw.2.2 hw.2.1).mpr hright).symm
    · have he := outside_or_deleted v _ _ hve
      rw [(indexedMatching P d).splice_fixed e v (Or.inr he),
        (indexedMatching P e).splice_fixed d v (Or.inl he)]
  · have hd' := outside_or_deleted v _ _ hvd
    rw [(indexedMatching P d).splice_fixed e v (Or.inl hd'),
      (indexedMatching P e).splice_fixed d v (Or.inr hd')]

end Paper2.Certificates.Q8.Atlas
