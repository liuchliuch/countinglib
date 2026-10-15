import Paper2.HighHeightReconstruction.EdgeTransfer

/-! Finite named-port selection and propagation of a shared matching edge. -/
namespace Paper2.HighHeightReconstruction
open CommonPhase EndpointSelfLoop MatchingPropagation
variable {ι : Type} [DecidableEq ι]

@[simp] theorem pairPorts_subset_iff (r : PortPair ι) (T : Finset ι) :
    pairPorts r ⊆ T ↔ r.first ∈ T ∧ r.second ∈ T := by
  simp only [pairPorts,Finset.insert_subset_iff,Finset.singleton_subset_iff]

theorem disjoint_of_subset (r s : PortPair ι) (T : Finset ι)
    (hr : pairPorts r ⊆ T) (hT : Disjoint T (pairPorts s)) : r.Disjoint s :=
  (pairPorts_disjoint r s).mpr (hT.mono_left hr)

theorem exists_pair_subset (T : Finset ι) (hT : 2 ≤ T.card) :
    ∃ r : PortPair ι, pairPorts r ⊆ T := by
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp (by omega : 1 < T.card)
  exact ⟨⟨a,b,hab⟩,(pairPorts_subset_iff _ T).mpr ⟨ha,hb⟩⟩

theorem exists_two_pairs_subset (T : Finset ι) (hT : 3 ≤ T.card) :
    ∃ r s : PortPair ι, pairPorts r ⊆ T ∧ pairPorts s ⊆ T ∧ ¬SamePair r s := by
  obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ := Finset.two_lt_card.mp (by omega : 2 < T.card)
  refine ⟨⟨a,b,hab⟩,⟨a,c,hac⟩,(pairPorts_subset_iff _ T).mpr ⟨ha,hb⟩,
    (pairPorts_subset_iff _ T).mpr ⟨ha,hc⟩,?_⟩
  rintro (⟨h₁,h₂⟩ | ⟨h₁,h₂⟩)
  · exact hbc h₂
  · exact hac h₁

theorem exists_pair_outside [Fintype ι] (U : Finset ι)
    (hn : U.card + 2 ≤ Fintype.card ι) :
    ∃ r : PortPair ι, Disjoint (pairPorts r) U := by
  have hdiff : 2 ≤ (Finset.univ \ U).card := by
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U)
    simp only [Finset.card_univ] at hh
    omega
  obtain ⟨r,hr⟩ := exists_pair_subset (Finset.univ \ U) hdiff
  refine ⟨r,Finset.disjoint_left.mpr ?_⟩
  intro a ha hU
  exact (Finset.mem_sdiff.mp (hr ha)).2 hU

/-- A triangle of deleted pairs carrying one edge makes it persistent on all
other pairs. Literal-X nonvanishing makes eight ports sufficient. -/
theorem edge_persistent_of_triangle [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ r, lam r ≠ 0) (e : PortPair ι)
    (T : Finset ι) (hT : T.card = 3) (hTe : Disjoint T (pairPorts e))
    (hknown : ∀ (r : PortPair ι) (hrT : pairPorts r ⊆ T),
      EdgeIn P r e (disjoint_of_subset r e T hrT hTe)) :
    ∀ (g : PortPair ι) (hge : g.Disjoint e), EdgeIn P g e hge := by
  intro g hge
  by_cases hgT : pairPorts g ⊆ T
  · exact hknown g hgT
  · obtain ⟨r,s,hrT,hsT,hrs⟩ := exists_two_pairs_subset T (by omega)
    have hre := disjoint_of_subset r e T hrT hTe
    have hse := disjoint_of_subset s e T hsT hTe
    have hr := hknown r hrT
    have hs := hknown s hsT
    by_cases hTg : Disjoint T (pairPorts g)
    · exact edge_in_of_two F lam P hd hnz r s g e hrs
        (disjoint_of_subset r g T hrT hTg) (disjoint_of_subset s g T hsT hTg)
        hre hse hge hr hs
    · have hinterpos : 0 < (T ∩ pairPorts g).card :=
        Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp hTg)
      have hUnion : (T ∪ pairPorts g).card ≤ 4 := by
        have hh := Finset.card_union_add_card_inter T (pairPorts g)
        simp only [hT,card_pairPorts] at hh
        omega
      have hinterlt : (T ∩ pairPorts g).card < 2 := by
        have hle := Finset.card_le_card (Finset.inter_subset_right (s₁ := T) (s₂ := pairPorts g))
        simp only [card_pairPorts] at hle
        by_contra hnot
        have heq : (T ∩ pairPorts g).card = (pairPorts g).card := by simp; omega
        have heqset : T ∩ pairPorts g = pairPorts g :=
          Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
        have hsub : T ∩ pairPorts g ⊆ T := Finset.inter_subset_left
        rw [heqset] at hsub
        exact hgT hsub
      have hdiff : 2 ≤ (T \ pairPorts g).card := by
        have hh := Finset.card_sdiff_add_card_inter T (pairPorts g)
        omega
      obtain ⟨k,hk⟩ := exists_pair_subset (T \ pairPorts g) hdiff
      have hkT : pairPorts k ⊆ T := fun a ha => (Finset.mem_sdiff.mp (hk ha)).1
      have hkg : k.Disjoint g := by
        apply (pairPorts_disjoint k g).mpr
        exact Finset.disjoint_left.mpr (fun a ha hb => (Finset.mem_sdiff.mp (hk ha)).2 hb)
      have hke := disjoint_of_subset k e T hkT hTe
      have hkedge := hknown k hkT
      let U := pairPorts e ∪ (T ∪ pairPorts g)
      have hU : U.card + 2 ≤ Fintype.card ι := by
        have hh := Finset.card_union_le (pairPorts e) (T ∪ pairPorts g)
        simp only [card_pairPorts] at hh
        dsimp [U]
        omega
      obtain ⟨t,htU⟩ := exists_pair_outside U hU
      have hte : t.Disjoint e := (pairPorts_disjoint t e).mpr
        (htU.mono_right (Finset.subset_union_left))
      have htT : Disjoint (pairPorts t) T := htU.mono_right (by
        intro a ha
        exact Finset.mem_union_right _ (Finset.mem_union_left _ ha))
      have htg : t.Disjoint g := (pairPorts_disjoint t g).mpr (htU.mono_right (by
        intro a ha
        exact Finset.mem_union_right _ (Finset.mem_union_right _ ha)))
      have hrt : r.Disjoint t := disjoint_of_subset r t T hrT htT.symm
      have hst : s.Disjoint t := disjoint_of_subset s t T hsT htT.symm
      have ht := edge_in_of_two F lam P hd hnz r s t e hrs hrt hst hre hse hte hr hs
      have hkt : k.Disjoint t := disjoint_of_subset k t T hkT htT.symm
      exact edge_in_of_two F lam P hd hnz k t g e (not_same_of_disjoint k t hkt)
        hkg htg hke hte hge hkedge ht

/-- A shared edge from two distinct cards gives a triangle whenever at least
three ports remain outside the two deleted pairs and the edge. -/
theorem edge_persistent_of_two [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ r, lam r ≠ 0)
    (r s e : PortPair ι) (hrs : ¬SamePair r s)
    (hre : r.Disjoint e) (hse : s.Disjoint e)
    (hr : EdgeIn P r e hre) (hs : EdgeIn P s e hse)
    (hroom : (pairPorts e ∪ (pairPorts r ∪ pairPorts s)).card + 3 ≤ Fintype.card ι) :
    ∀ (g : PortPair ι) (hge : g.Disjoint e), EdgeIn P g e hge := by
  let U := pairPorts e ∪ (pairPorts r ∪ pairPorts s)
  have hdiff : 3 ≤ (Finset.univ \ U).card := by
    have hh := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ U)
    simp only [Finset.card_univ] at hh
    change U.card + 3 ≤ Fintype.card ι at hroom
    omega
  obtain ⟨T,hTU,hT⟩ := Finset.exists_subset_card_eq hdiff
  have hTavoid : Disjoint T U := Finset.disjoint_left.mpr (fun a ha hb =>
    (Finset.mem_sdiff.mp (hTU ha)).2 hb)
  have hTe : Disjoint T (pairPorts e) := hTavoid.mono_right Finset.subset_union_left
  apply edge_persistent_of_triangle hn F lam P hd hnz e T hT hTe
  intro g hg
  have hgU : Disjoint (pairPorts g) U := hTavoid.mono_left hg
  have hgr : g.Disjoint r := (pairPorts_disjoint g r).mpr (hgU.mono_right (by
    intro a ha
    exact Finset.mem_union_right _ (Finset.mem_union_left _ ha)))
  have hgs : g.Disjoint s := (pairPorts_disjoint g s).mpr (hgU.mono_right (by
    intro a ha
    exact Finset.mem_union_right _ (Finset.mem_union_right _ ha)))
  exact edge_in_of_two F lam P hd hnz r s g e hrs hgr.symm hgs.symm hre hse
    (disjoint_of_subset g e T hg hTe) hr hs

end Paper2.HighHeightReconstruction
