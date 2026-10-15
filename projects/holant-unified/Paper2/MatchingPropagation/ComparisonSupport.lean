import Paper2.MatchingPropagation.TwoComparisons

namespace Paper2.MatchingPropagation
open CommonPhase EndpointSelfLoop
variable {ι : Type}

def SamePair (e f : PortPair ι) : Prop :=
  (e.first = f.first ∧ e.second = f.second) ∨
    (e.first = f.second ∧ e.second = f.first)

theorem SamePair.symm {e f : PortPair ι} (h : SamePair e f) : SamePair f e := by
  rcases h with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact Or.inl ⟨ha.symm,hb.symm⟩
  · exact Or.inr ⟨hb.symm,ha.symm⟩

theorem not_same_of_disjoint (e f : PortPair ι) (h : e.Disjoint f) : ¬SamePair e f := by
  rintro (⟨ha,hb⟩ | ⟨ha,hb⟩)
  · exact h.1 ha
  · exact h.2.1 ha

theorem residual_disjoint (e r s : PortPair ι) (her : e.Disjoint r)
    (hes : e.Disjoint s) (hrs : r.Disjoint s) :
    (e.residual r her).Disjoint (e.residual s hes) :=
  ⟨fun h => hrs.1 (congrArg Subtype.val h),
    fun h => hrs.2.1 (congrArg Subtype.val h),
    fun h => hrs.2.2.1 (congrArg Subtype.val h),
    fun h => hrs.2.2.2 (congrArg Subtype.val h)⟩

theorem extend_other (e : PortPair ι) (x : Remaining e.first e.second → Bool)
    (t : Bool) (a : ι) (ha₁ : a ≠ e.first) (ha₂ : a ≠ e.second) :
    extendPair e.first e.second e.distinct x t a = x ⟨a,ha₁,ha₂⟩ := by
  classical
  simp [extendPair,splitPorts,ha₁,ha₂,Sum.elim]

/-- A concrete support constraint transfers across the two orders of deletion. -/
theorem double_forces_transfer (F : Tensor ℂ ι) (e s r : PortPair ι)
    (hes : e.Disjoint s) (her : e.Disjoint r) (hsr : s.Disjoint r)
    (hforce : Forces ((e.residual s hes).pairSum (contraction F e))
      (e.residual r her).first (e.residual r her).second) :
    Forces ((s.residual e hes.symm).pairSum (contraction F s))
      (s.residual r hsr).first (s.residual r hsr).second := by
  intro y hy
  let x := extendPair s.first s.second s.distinct y false
  have hd := double_loop_eq F e s hes x
  have hnz : (e.residual s hes).pairSum (contraction F e)
      (restrict e.first e.second x) ≠ 0 := by
    rw [hd]
    simpa only [x,PortPair.restrict_extend] using hy
  have hh := hforce (restrict e.first e.second x) hnz
  change x r.second = !(x r.first) at hh
  simpa only [x,extend_other s y false r.second hsr.2.1.symm hsr.2.2.2.symm,
    extend_other s y false r.first hsr.1.symm hsr.2.2.1.symm,PortPair.residual] using hh

theorem Forces.mul_iff (c : ℂ) (hc : c ≠ 0) (F : Tensor ℂ ι) (a b : ι) :
    Forces (fun x => c * F x) a b ↔ Forces F a b := by
  constructor
  · intro h x hx
    exact h x (mul_ne_zero hc hx)
  · intro h x hx
    exact h x (fun hz => hx (by simp [hz]))

/-- The exceptional pair consists of the actual mates in the second matching. -/
noncomputable def matePair (s r : PortPair ι) (hsr : s.Disjoint r)
    (Q : Matching (Remaining s.first s.second)) : PortPair ι where
  first := (mate Q (s.residual r hsr).first).val
  second := (mate Q (s.residual r hsr).second).val
  distinct := by
    intro h
    exact (s.residual r hsr).distinct (mate_injective Q (Subtype.ext h))

/-- Any newly forced edge under the second comparison identifies the deleted
pair with the unique exceptional mate pair. -/
theorem comparison_forces_same_matePair (F : Tensor ℂ ι) (e s r : PortPair ι)
    (hes : e.Disjoint s) (her : e.Disjoint r) (hsr : s.Disjoint r)
    (Q : Matching (Remaining s.first s.second)) (c : ℂ) (hc : c ≠ 0)
    (hs : contraction F s = fun x => c * literal Q ℂ x)
    (hm : mate Q (s.residual r hsr).first ≠ (s.residual r hsr).second)
    (hforce : Forces ((e.residual s hes).pairSum (contraction F e))
      (e.residual r her).first (e.residual r her).second) :
    SamePair e (matePair s r hsr Q) := by
  have ht := double_forces_transfer F e s r hes her hsr hforce
  rw [hs,PortPair.pairSum_mul] at ht
  have ht' := (Forces.mul_iff c hc _ _ _).mp ht
  let R := s.residual r hsr
  let E := s.residual e hes.symm
  have hRE : R.Disjoint E := residual_disjoint s r e hsr hes.symm her.symm
  have hm' := literal_forces_deleted_mates Q E R.first R.second R.distinct hm
    hRE.1 hRE.2.1 hRE.2.2.1 hRE.2.2.2 ht'
  rcases hm' with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Or.inl ⟨(congrArg Subtype.val h₁).symm,(congrArg Subtype.val h₂).symm⟩
  · exact Or.inr ⟨(congrArg Subtype.val h₂).symm,(congrArg Subtype.val h₁).symm⟩

/-- The nonexceptional pairs in W of the manuscript's condition-2 proof. -/
theorem nonexceptional_isX (F : Tensor ℂ ι) (hd : WeightedDeck F)
    (r s : PortPair ι) (hrs : r.Disjoint s) (hr : XAt F r)
    (Q : Matching (Remaining s.first s.second)) (c : ℂ) (hc : c ≠ 0)
    (hs : contraction F s = fun x => c * literal Q ℂ x)
    (hm : mate Q (s.residual r hrs.symm).first ≠ (s.residual r hrs.symm).second)
    (e : PortPair ι) (her : e.Disjoint r) (hes : e.Disjoint s)
    (hne : ¬SamePair e (matePair s r hrs.symm Q)) : XAt F e := by
  have hsX : XAt F s := ⟨Q,c,hc,hs⟩
  obtain ⟨P,p,q,d,hdn,hp,hq,he⟩ := hd e (nonzero_of_disjoint_X F e r her hr)
  obtain ⟨hrn,hrf⟩ := double_comparison F e r her hr
  obtain ⟨hsn,hsf⟩ := double_comparison F e s hes hsX
  rw [he] at hrn hrf hsn hsf
  rw [XAt,he]
  apply weighted_isX_of_two_flat P p q d hdn hp hq (e.residual r her) (e.residual s hes)
    (residual_disjoint e r s her hes hrs) hrn hsn hrf hsf
  intro hforce
  apply hne
  apply comparison_forces_same_matePair F e s r hes her hrs.symm Q c hc hs hm
  simpa only [he] using hforce

end Paper2.MatchingPropagation
