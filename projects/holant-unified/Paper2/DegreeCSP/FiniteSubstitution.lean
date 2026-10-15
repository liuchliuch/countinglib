import Paper2.NetworkSubstitution

/-! Finite-index native substitution keeps the explicitly chosen outer
variable/occurrence order available to a raw record compiler. It is the same
literal graph construction as ordered Network substitution, before enumerating
the finite outer indices by Fin. -/
namespace Paper2.DegreeCSP.FiniteSubstitution
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {K V E : Type} {n : ℕ}
variable (G : FiniteNetwork K V E n)
variable (R : (v : V) → Network K (G.arity v))

abbrev Vertices := Σ v : V,Fin (R v).shape.vertices
abbrev InnerEdges := Σ v : V,Fin (R v).shape.edges
abbrev Edges := E ⊕ InnerEdges G R

def graph : FiniteNetwork K (Vertices G R) (Edges G R) n where
  arity p := (R p.1).shape.arity p.2
  ports := (Equiv.sigmaAssoc (fun v w => Fin ((R v).shape.arity w))).trans
    ((Equiv.sigmaCongrRight (fun v => (R v).shape.ports)).trans
      ((Equiv.sigmaSumDistrib (fun v => Fin (G.arity v))
          (fun v => Fin (R v).shape.edges × Bool)).trans
        ((Equiv.sumCongr G.ports
            (Equiv.sigmaProdDistrib (fun v => Fin (R v).shape.edges) Bool).symm).trans
          ((Equiv.sumAssoc _ _ _).trans
            (Equiv.sumCongr (Equiv.refl _)
              (Equiv.sumProdDistrib E (InnerEdges G R) Bool).symm)))))
  vertex p := (R p.1).vertex p.2
  edge := Sum.elim G.edge (fun p => (R p.1).edge p.2)

def assignments : (Edges G R → Bool) ≃
    ((E → Bool) × ((v : V) → Fin (R v).shape.edges → Bool)) where
  toFun z := (fun e => z (.inl e),fun v e => z (.inr ⟨v,e⟩))
  invFun p := Sum.elim p.1 (fun q => p.2 q.1 q.2)
  left_inv := by intro z; funext e; rcases e with e | ⟨v,e⟩ <;> rfl
  right_inv := by intro p; rfl

variable [Fintype V] [Fintype E] [CommSemiring K]

omit [Fintype V] [Fintype E] in
theorem graph_nativeX (hG : ∀ e,G.edge e = Signature.disequality)
    (hR : ∀ v,(R v).NativeX) : ∀ e,(graph G R).edge e = Signature.disequality := by
  rintro (e | ⟨v,e⟩)
  · exact hG e
  · exact hR v e

theorem graph_denote (hG : ∀ e,G.edge e = Signature.disequality)
    (hR : ∀ v,(R v).NativeX) (hden : ∀ v,(R v).denote = G.vertex v) :
    (graph G R).denote = G.denote := by
  classical
  let : DecidableEq (Edges G R) := Classical.decEq _
  funext x
  rw [FiniteNetwork.denote_nativeX _ (graph_nativeX G R hG hR)]
  rw [← (assignments G R).symm.sum_comp]
  rw [FiniteNetwork.denote_nativeX G hG x]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr (by ext; simp) ?_
  intro z _
  have hlocal : ∀ v,G.vertex v (fun i => Sum.elim x
        (fun q : E × Bool => if q.2 then !(z q.1) else z q.1)
        (G.ports ⟨v,i⟩)) =
      ∑ w : Fin (R v).shape.edges → Bool,∏ u,(R v).vertex u (fun j => Sum.elim
        (fun i => Sum.elim x
          (fun q : E × Bool => if q.2 then !(z q.1) else z q.1) (G.ports ⟨v,i⟩))
        (fun q : Fin (R v).shape.edges × Bool => if q.2 then !(w q.1) else w q.1)
        ((R v).shape.ports ⟨u,j⟩)) := by
    intro v
    rw [← hden v]
    exact (R v).denote_nativeX (hR v) _
  simp only [hlocal]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr (by ext; simp) ?_
  intro w _
  rw [Fintype.prod_sigma]
  apply Finset.prod_congr rfl
  intro v _
  apply Finset.prod_congr rfl
  intro u _
  congr 1
  funext j
  dsimp [graph,assignments,Equiv.sigmaAssoc,Equiv.sigmaCongrRight]
  generalize hr : (R v).shape.ports ⟨u,j⟩ = q
  cases q with
  | inl i =>
    generalize hg : G.ports ⟨v,i⟩ = p
    cases p <;> simp_all [Equiv.sigmaSumDistrib,Equiv.sumCongr,Equiv.sumAssoc,
      Equiv.sumProdDistrib,Equiv.sigmaProdDistrib]
  | inr p => simp_all [Equiv.sigmaSumDistrib,Equiv.sumCongr,Equiv.sumAssoc,
      Equiv.sumProdDistrib,Equiv.sigmaProdDistrib]

omit [CommSemiring K] in
theorem graph_uses (F : SignatureFamily K) (hR : ∀ v,(R v).Uses F) :
    (graph G R).toNetwork.Uses F := by
  intro p
  exact hR _ _

end
end Paper2.DegreeCSP.FiniteSubstitution
