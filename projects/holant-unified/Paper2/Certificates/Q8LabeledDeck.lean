import Paper2.Certificates.Q8LabeledGeometry

/-! Actual X-contraction equations, in arbitrary verified F₂³ port labels,
imply the exact coefficient swap system used by the Reed–Muller theorem. -/
namespace Paper2.Certificates.Q8.Atlas
open CommonPhase EndpointSelfLoop ReedMuller

variable {K : Type*} [CommRing K]

def MatchingLabels
    (P : (e : PortPair Port) → XMatching (EndpointSelfLoop.Remaining e.first e.second))
    (p : Equiv.Perm Port) : Prop :=
  ∀ d v, v ≠ (deleted d).1 → v ≠ (deleted d).2 →
    p ((indexedMatching P d).extend v) =
      Fin.xor (p v) (Fin.xor (p (deleted d).1) (p (deleted d).2))

theorem indexedMatching_extend
    (P : (e : PortPair Port) → XMatching (EndpointSelfLoop.Remaining e.first e.second))
    (d : PairIndex) (v : Port) (hv : v ≠ (deleted d).1 ∧ v ≠ (deleted d).2) :
    (indexedMatching P d).extend v =
      (MatchingPropagation.mate (P (portPair d)) ⟨v,hv⟩).val := by
  rw [Matching.extend,dif_pos hv]
  rfl

theorem transversal_labels
    (P : (e : PortPair Port) → XMatching (EndpointSelfLoop.Remaining e.first e.second))
    (p : Equiv.Perm Port) (h : MatchingLabels P p) (d : PairIndex) (x : Word) :
    Transversal (P (portPair d)) (restrict (portPair d).first (portPair d).second (fun v => x (p v))) ↔
      TranslationAt (p (deleted d).1) (p (deleted d).2) x := by
  rw [MatchingPropagation.transversal_iff_mate]
  constructor
  · intro ht w hw1 hw2
    have hv : p.symm w ≠ (deleted d).1 ∧ p.symm w ≠ (deleted d).2 := by
      constructor
      · intro he
        exact hw1 (p.symm_apply_eq.mp he)
      · intro he
        exact hw2 (p.symm_apply_eq.mp he)
    let v : EndpointSelfLoop.Remaining (portPair d).first (portPair d).second := ⟨p.symm w,hv⟩
    have hh := ht v
    change x (p (MatchingPropagation.mate (P (portPair d)) v).val) = !(x (p v.val)) at hh
    have hm := h d v.val v.property.1 v.property.2
    rw [indexedMatching_extend P d v.val v.property] at hm
    rw [hm] at hh
    simpa only [v,p.apply_symm_apply] using hh
  · intro ht v
    have hm := h d v.val v.property.1 v.property.2
    rw [indexedMatching_extend P d v.val v.property] at hm
    change x (p (MatchingPropagation.mate (P (portPair d)) v).val) = !(x (p v.val))
    exact (congrArg x hm).trans (ht (p v.val)
      (fun hh => v.property.1 (p.injective hh)) (fun hh => v.property.2 (p.injective hh)))

def labeledPair (p : Equiv.Perm Port) (e : PortPair Port) : PortPair Port :=
  ⟨p e.first,p e.second,fun h => e.distinct (p.injective h)⟩

theorem fill_labels (p : Equiv.Perm Port) (e : PortPair Port) (x : Word) (t : Bool) :
    e.fill (fun v => x (p v)) t = fun v => (labeledPair p e).fill x t (p v) := by
  funext v
  simp only [PortPair.fill,labeledPair,Equiv.apply_eq_iff_eq]

theorem pairSum_labels (p : Equiv.Perm Port) (e : PortPair Port)
    (F : Signature K 8) (x : Word) :
    e.pairSum F (fun v => x (p v)) = (labeledPair p e).pairSum (labeledTensor p F) x := by
  unfold PortPair.pairSum
  apply Finset.sum_congr rfl
  intro t ht
  rw [fill_labels]
  rfl

theorem fill_original (e : PortPair Port) (x : Word) (t : Bool)
    (hfirst : x e.first = t) (hsecond : x e.second = !t) : e.fill x t = x := by
  funext v
  by_cases h1 : v = e.first
  · subst v
    simp only [PortPair.fill,ite_true,hfirst]
  · by_cases h2 : v = e.second
    · subst v
      simp only [PortPair.fill,if_neg h1,ite_true,hsecond]
    · simp only [PortPair.fill,if_neg h1,if_neg h2]

theorem pairSum_crossing (e : PortPair Port) (F : Signature K 8) (p q : Port) (x : Word)
    (hp : x p = true) (hq : x q = false)
    (he : (e.first = p ∧ e.second = q) ∨ (e.first = q ∧ e.second = p)) :
    e.pairSum F x = F x + F (swap x p q) := by
  rcases he with he | he
  · have htrue : e.fill x true = x := fill_original e x true (he.1 ▸ hp) (he.2 ▸ hq)
    have hfalse : e.fill x false = swap x p q := by
      funext v
      simp only [PortPair.fill,swap,he.1,he.2,Bool.not_false]
    simp only [PortPair.pairSum,Fintype.sum_bool,htrue,hfalse]
  · have hfalse : e.fill x false = x := fill_original e x false (he.1 ▸ hq) (he.2 ▸ hp)
    have htrue : e.fill x true = swap x p q := by
      have hpq : p ≠ q := fun hh => Bool.noConfusion (hp.symm.trans (hh.symm ▸ hq))
      funext v
      by_cases hvp : v = p
      · subst v
        simp only [PortPair.fill,swap,he.1,he.2,hpq,ite_false,ite_true,Bool.not_true]
      · by_cases hvq : v = q <;>
          simp only [PortPair.fill,swap,he.1,he.2,hvp,hvq,ite_false,ite_true,Bool.not_true,Ne.symm hpq]
    simp only [PortPair.pairSum,Fintype.sum_bool,htrue,hfalse]
    exact add_comm _ _

def labeledScale (lam : PortPair Port → K) (p : Equiv.Perm Port) (a b : Port) : K :=
  lam (portPair (pairIndex (p.symm a) (p.symm b)))

theorem labeledScale_symmetric (lam : PortPair Port → K) (p : Equiv.Perm Port) (a b : Port) :
    labeledScale lam p a b = labeledScale lam p b a := by
  unfold labeledScale
  rw [pairIndex_symmetric]

theorem labeled_deck_swap_system (F : Signature K 8) (lam : PortPair Port → K)
    (P : (e : PortPair Port) → XMatching (EndpointSelfLoop.Remaining e.first e.second))
    (hd : MatchingDeck F lam P) (p : Equiv.Perm Port) (hl : MatchingLabels P p) :
    SwapSystem (labeledTensor p F) (labeledScale lam p) := by
  classical
  intro x a b hw ha hb
  have hab : a ≠ b := fun hh => Bool.noConfusion (ha.symm.trans (hh.symm ▸ hb))
  let d := pairIndex (p.symm a) (p.symm b)
  have he := pairIndex_endpoints (p.symm a) (p.symm b) (fun hh => hab (p.symm.injective hh))
  have hend : ((labeledPair p (portPair d)).first = a ∧ (labeledPair p (portPair d)).second = b) ∨
      ((labeledPair p (portPair d)).first = b ∧ (labeledPair p (portPair d)).second = a) := by
    rcases he with he | he
    · left
      simp only [labeledPair,portPair,d,he,p.apply_symm_apply,true_and]
    · right
      simp only [labeledPair,portPair,d,he,p.apply_symm_apply,true_and]
  have ht : TranslationAt (p (deleted d).1) (p (deleted d).2) x ↔ TranslationAt a b x := by
    rcases hend with he | he
    · change p (deleted d).1 = a ∧ p (deleted d).2 = b at he
      rw [he.1,he.2]
    · change p (deleted d).1 = b ∧ p (deleted d).2 = a at he
      rw [he.1,he.2]
      exact ⟨TranslationAt.swap,TranslationAt.swap⟩
  have hv := congrFun (PortPair.pairSum_deck hd (portPair d)) (fun v => x (p v))
  rw [pairSum_labels,pairSum_crossing _ _ a b x ha hb hend] at hv
  have ht' := (transversal_labels P p hl d x).trans ht
  rw [literal,ht',translationAt_iff_transversal a b x hab,
    translation_transversal_iff a b x hw ha hb] at hv
  simpa only [labeledScale,d,mul_ite,mul_one,mul_zero] using hv

theorem labeled_rm_weight (p : Equiv.Perm Port) (x : Word) :
    ReedMuller.weight (fun v => x (p v)) = ReedMuller.weight x := by
  unfold ReedMuller.weight
  exact Fintype.sum_equiv p _ _ (fun _ => rfl)

/-- The tensor-level RM(1,3) conclusion retains the actual port labeling. -/
theorem scalar_central_of_labeled_deck [NoZeroDivisors K] [CharZero K]
    (F : Signature K 8) (lam : PortPair Port → K)
    (P : (e : PortPair Port) → XMatching (EndpointSelfLoop.Remaining e.first e.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ e, lam e ≠ 0)
    (p : Equiv.Perm Port) (hl : MatchingLabels P p)
    (heo : ∀ x, ReedMuller.weight x ≠ 4 → F x = 0) :
    ∃ c : K, c ≠ 0 ∧ labeledTensor p F = fun x => c * central x := by
  apply scalar_central_of_swap_system (labeledTensor p F) (labeledScale lam p)
    (labeled_deck_swap_system F lam P hd p hl) (labeledScale_symmetric lam p)
  · intro a b hab
    exact hnz _
  · intro x hx
    apply heo
    rwa [labeled_rm_weight]

end Paper2.Certificates.Q8.Atlas
