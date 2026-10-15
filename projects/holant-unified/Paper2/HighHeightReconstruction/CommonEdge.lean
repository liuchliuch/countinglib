import Paper2.HighHeightReconstruction.EdgeTransfer

/-! A first shared edge is forced by actual double-deletion support. -/
namespace Paper2.HighHeightReconstruction
open CommonPhase EndpointSelfLoop MatchingPropagation
variable {ι : Type}

theorem originalEdge_disjoint (r : PortPair ι) (Q : Matching (Remaining r.first r.second))
    (j : Fin Q.count) : (originalEdge r Q j).Disjoint r :=
  ⟨(Q.ports (j,false)).property.1,(Q.ports (j,false)).property.2,
    (Q.ports (j,true)).property.1,(Q.ports (j,true)).property.2⟩

theorem originalEdges_disjoint (r : PortPair ι) (Q : Matching (Remaining r.first r.second))
    (j k : Fin Q.count) (hjk : j ≠ k) : (originalEdge r Q j).Disjoint (originalEdge r Q k) := by
  have hh (a b : Bool) : (Q.ports (j,a)).val ≠ (Q.ports (k,b)).val := by
    intro h
    exact hjk (congrArg Prod.fst (Q.ports.injective (Subtype.ext h)))
  exact ⟨hh false false,hh false true,hh true false,hh true true⟩

theorem originalEdge_edgeIn (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (r : PortPair ι) (j : Fin (P r).count) :
    EdgeIn P r (originalEdge r (P r) j) (originalEdge_disjoint r (P r) j).symm := by
  change mate (P r) ((P r).ports (j,false)) = (P r).ports (j,true)
  simp

/-- Taking mates twice recovers the named unordered pair. -/
theorem same_matePair_injective (s e f : PortPair ι) (hse : s.Disjoint e)
    (hsf : s.Disjoint f) (Q : Matching (Remaining s.first s.second))
    (h : SamePair (matePair s e hse Q) (matePair s f hsf Q)) : SamePair e f := by
  rcases h with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · exact Or.inl ⟨congrArg Subtype.val (mate_injective Q (Subtype.ext h₁)),
      congrArg Subtype.val (mate_injective Q (Subtype.ext h₂))⟩
  · exact Or.inr ⟨congrArg Subtype.val (mate_injective Q (Subtype.ext h₁)),
      congrArg Subtype.val (mate_injective Q (Subtype.ext h₂))⟩

/-- A double contraction can create only one new edge: among two different
surviving edges in the first card, one must already be in the second card. -/
theorem one_of_two_edges_shared (F : Tensor ℂ ι) (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ r, lam r ≠ 0)
    (r s e f : PortPair ι) (hrs : r.Disjoint s)
    (hre : r.Disjoint e) (hse : s.Disjoint e)
    (hrf : r.Disjoint f) (hsf : s.Disjoint f) (hef : ¬SamePair e f)
    (he : EdgeIn P r e hre) (hf : EdgeIn P r f hrf) :
    EdgeIn P s e hse ∨ EdgeIn P s f hsf := by
  by_contra h
  push Not at h
  have he' := comparison_forces_same_matePair F r s e hrs hre hse (P s) (lam s)
    (hnz s) (hd s) h.1 (deck_pairSum_forces_edge F lam P hd r s e hrs hre hse.symm he)
  have hf' := comparison_forces_same_matePair F r s f hrs hrf hsf (P s) (lam s)
    (hnz s) (hd s) h.2 (deck_pairSum_forces_edge F lam P hd r s f hrs hrf hsf.symm hf)
  exact hef (same_matePair_injective s e f hse hsf (P s) (he'.symm.trans hf'))

/-- Every literal deck on at least eight ports has two distinct (here disjoint)
deleted pairs sharing one actual residual matching edge. -/
theorem exists_shared_edge [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ r, lam r ≠ 0) (r : PortPair ι) :
    ∃ (s e : PortPair ι) (hrs : r.Disjoint s) (hre : r.Disjoint e) (hse : s.Disjoint e),
      EdgeIn P r e hre ∧ EdgeIn P s e hse := by
  have hcard := Fintype.card_congr (P r).ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hcard
  have hrem := remaining_card r.first r.second r.distinct
  have hcount : 3 ≤ (P r).count := by omega
  let j₀ : Fin (P r).count := ⟨0,by omega⟩
  let j₁ : Fin (P r).count := ⟨1,by omega⟩
  let j₂ : Fin (P r).count := ⟨2,by omega⟩
  have h₀₁ : j₀ ≠ j₁ := by intro h; have := congrArg Fin.val h; simp [j₀,j₁] at this
  have h₀₂ : j₀ ≠ j₂ := by intro h; have := congrArg Fin.val h; simp [j₀,j₂] at this
  have h₁₂ : j₁ ≠ j₂ := by intro h; have := congrArg Fin.val h; simp [j₁,j₂] at this
  let s := originalEdge r (P r) j₀
  let e := originalEdge r (P r) j₁
  let f := originalEdge r (P r) j₂
  have hrs : r.Disjoint s := (originalEdge_disjoint r (P r) j₀).symm
  have hre : r.Disjoint e := (originalEdge_disjoint r (P r) j₁).symm
  have hrf : r.Disjoint f := (originalEdge_disjoint r (P r) j₂).symm
  have hse : s.Disjoint e := originalEdges_disjoint r (P r) j₀ j₁ h₀₁
  have hsf : s.Disjoint f := originalEdges_disjoint r (P r) j₀ j₂ h₀₂
  have hef : ¬SamePair e f := not_same_of_disjoint e f (originalEdges_disjoint r (P r) j₁ j₂ h₁₂)
  have he := originalEdge_edgeIn P r j₁
  have hf := originalEdge_edgeIn P r j₂
  rcases one_of_two_edges_shared F lam P hd hnz r s e f hrs hre hse hrf hsf hef he hf with h | h
  · exact ⟨s,e,hrs,hre,hse,he,h⟩
  · exact ⟨s,f,hrs,hrf,hsf,hf,h⟩

end Paper2.HighHeightReconstruction
