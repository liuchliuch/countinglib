import Paper2.MatchingPropagation.ComparisonSupport

namespace Paper2.MatchingPropagation
open CommonPhase EndpointSelfLoop
variable {ι : Type}

/-- A two-port factor must avoid one of three pairwise disjoint pairs. -/
theorem disjoint_one_of_three (f r s t : PortPair ι)
    (hrs : r.Disjoint s) (hrt : r.Disjoint t) (hst : s.Disjoint t) :
    f.Disjoint r ∨ f.Disjoint s ∨ f.Disjoint t := by
  by_contra h
  push Not at h
  obtain ⟨hfr,hfs,hft⟩ := h
  simp only [PortPair.Disjoint, not_and_or, not_not] at hfr hfs hft
  obtain ⟨hrs₁,hrs₂,hrs₃,hrs₄⟩ := hrs
  obtain ⟨hrt₁,hrt₂,hrt₃,hrt₄⟩ := hrt
  obtain ⟨hst₁,hst₂,hst₃,hst₄⟩ := hst
  rcases hfr with hfr | hfr | hfr | hfr <;>
    rcases hfs with hfs | hfs | hfs | hfs <;>
    rcases hft with hft | hft | hft | hft <;> aesop

/-- Three known disjoint X contractions suffice to determine every factor of
another contraction disjoint from all three. -/
theorem isX_of_three_disjoint (F : Tensor ℂ ι) (hd : WeightedDeck F)
    (e r s t : PortPair ι) (her : e.Disjoint r) (hes : e.Disjoint s) (het : e.Disjoint t)
    (hrs : r.Disjoint s) (hrt : r.Disjoint t) (hst : s.Disjoint t)
    (hr : XAt F r) (hs : XAt F s) (ht : XAt F t) : XAt F e := by
  obtain ⟨P,p,q,c,hc,hp,hq,he⟩ := hd e (nonzero_of_disjoint_X F e r her hr)
  rw [XAt,he]
  apply weighted_isX_of_equal P p q c hc hp
  intro j
  rcases disjoint_one_of_three (originalEdge e P j) r s t hrs hrt hst with h | h | h
  · exact factor_eq_of_disjoint_X F e r her hr P p q c hp hq he j
      (avoids_of_disjoint_original e r her P j h)
  · exact factor_eq_of_disjoint_X F e s hes hs P p q c hp hq he j
      (avoids_of_disjoint_original e s hes P j h)
  · exact factor_eq_of_disjoint_X F e t het ht P p q c hp hq he j
      (avoids_of_disjoint_original e t het P j h)

noncomputable def pairPorts (e : PortPair ι) : Finset ι := by
  classical
  exact {e.first,e.second}

@[simp] theorem mem_pairPorts (e : PortPair ι) (a : ι) :
    a ∈ pairPorts e ↔ a = e.first ∨ a = e.second := by
  classical
  simp [pairPorts]

@[simp] theorem card_pairPorts (e : PortPair ι) : (pairPorts e).card = 2 := by
  classical
  simp [pairPorts,e.distinct]

theorem pairPorts_disjoint (e f : PortPair ι) :
    e.Disjoint f ↔ Disjoint (pairPorts e) (pairPorts f) := by
  classical
  simp [PortPair.Disjoint,Finset.disjoint_left,pairPorts,and_assoc]

theorem pairPorts_union_le_three [DecidableEq ι] (e f : PortPair ι) (h : ¬e.Disjoint f) :
    (pairPorts e ∪ pairPorts f).card ≤ 3 := by
  classical
  have hi : (pairPorts e ∩ pairPorts f).Nonempty :=
    Finset.not_disjoint_iff_nonempty_inter.mp (mt (pairPorts_disjoint e f).mpr h)
  have hc := Finset.card_pos.mpr hi
  have hh := Finset.card_union_add_card_inter (pairPorts e) (pairPorts f)
  simp only [card_pairPorts] at hh
  omega

/-- Two overlaps reduce the excluded ports from eight to at most six. -/
theorem exists_disjoint_four [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (r s e f : PortPair ι) (hse : ¬s.Disjoint e) (hrf : ¬r.Disjoint f) :
    ∃ t : PortPair ι, r.Disjoint t ∧ s.Disjoint t ∧ e.Disjoint t ∧ f.Disjoint t := by
  classical
  let U := (pairPorts s ∪ pairPorts e) ∪ (pairPorts r ∪ pairPorts f)
  have hu : U.card ≤ 6 := by
    have h₁ := pairPorts_union_le_three s e hse
    have h₂ := pairPorts_union_le_three r f hrf
    have h₃ := Finset.card_union_le (pairPorts s ∪ pairPorts e) (pairPorts r ∪ pairPorts f)
    dsimp [U]
    omega
  have hcard : 1 < (Finset.univ \ U).card := by
    have hh := Finset.card_sdiff_add_card_eq_card (show U ⊆ Finset.univ from Finset.subset_univ _)
    simp only [Finset.card_univ] at hh
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hcard
  have ha' : a ≠ s.first ∧ a ≠ s.second ∧ a ≠ e.first ∧ a ≠ e.second ∧
      a ≠ r.first ∧ a ≠ r.second ∧ a ≠ f.first ∧ a ≠ f.second := by
    simpa [U,and_assoc] using (Finset.mem_sdiff.mp ha).2
  have hb' : b ≠ s.first ∧ b ≠ s.second ∧ b ≠ e.first ∧ b ≠ e.second ∧
      b ≠ r.first ∧ b ≠ r.second ∧ b ≠ f.first ∧ b ≠ f.second := by
    simpa [U,and_assoc] using (Finset.mem_sdiff.mp hb).2
  refine ⟨⟨a,b,hab⟩,?_,?_,?_,?_⟩ <;> unfold PortPair.Disjoint <;> simp only <;> tauto

/-- Once all W-pairs are X, the remaining pairs avoiding the fixed first pair
follow by a genuinely surviving-factor comparison. -/
theorem extend_from_common_complement [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hd : WeightedDeck F) (r s : PortPair ι)
    (hr : XAt F r) (hW : ∀ e, e.Disjoint r → e.Disjoint s → XAt F e) :
    ∀ e, e.Disjoint r → XAt F e := by
  intro e her
  by_cases hes : e.Disjoint s
  · exact hW e her hes
  · obtain ⟨P,p,q,c,hc,hp,hq,he⟩ := hd e (nonzero_of_disjoint_X F e r her hr)
    rw [XAt,he]
    apply weighted_isX_of_equal P p q c hc hp
    intro j
    by_cases hjr : (originalEdge e P j).Disjoint r
    · exact factor_eq_of_disjoint_X F e r her hr P p q c hp hq he j
        (avoids_of_disjoint_original e r her P j hjr)
    · have hse : ¬s.Disjoint e := fun h => hes h.symm
      have hrj : ¬r.Disjoint (originalEdge e P j) := fun h => hjr h.symm
      obtain ⟨t,hrt,hst,het,hjt⟩ := exists_disjoint_four hn r s e (originalEdge e P j) hse hrj
      exact factor_eq_of_disjoint_X F e t het (hW t hrt.symm hst.symm) P p q c hp hq he j
        (avoids_of_disjoint_original e t het P j hjt)

end Paper2.MatchingPropagation
