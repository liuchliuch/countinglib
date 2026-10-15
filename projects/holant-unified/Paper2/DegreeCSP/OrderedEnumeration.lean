import Paper2.NetworkRealization

/-! A prescribed vertex and edge enumeration retains every local port ordinal.
This connects the finite semantic graph to deterministic raw prefix indices. -/
namespace Paper2.DegreeCSP.OrderedEnumeration
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K V E : Type} {n vCount eCount : ℕ}
variable (G : FiniteNetwork K V E n) (ve : V ≃ Fin vCount) (ee : E ≃ Fin eCount)

def graph : Network K n where
  shape := {
    vertices := vCount
    arity v := G.arity (ve.symm v)
    edges := eCount
    ports := (Equiv.sigmaCongrLeft ve.symm).trans
      (G.ports.trans (Equiv.sumCongr (Equiv.refl _)
        (Equiv.prodCongr ee (Equiv.refl _)))) }
  vertex v := G.vertex (ve.symm v)
  edge e := G.edge (ee.symm e)

variable [Fintype V] [Fintype E] [CommSemiring K]

theorem graph_denote : (graph G ve ee).denote = G.denote := by
  classical
  funext x
  unfold Network.denote FiniteNetwork.denote
  apply Fintype.sum_equiv
    (Equiv.arrowCongr (Equiv.prodCongr ee.symm (Equiv.refl Bool)) (Equiv.refl Bool))
  intro z
  apply congrArg₂ (· * ·)
  · apply Fintype.prod_equiv ve.symm
    intro v
    congr 1
    funext i
    dsimp [graph,NetworkShape.assignment]
    change Sum.elim x z ((Equiv.sumCongr (Equiv.refl _)
      (Equiv.prodCongr ee (Equiv.refl _))) (G.ports ⟨ve.symm v,i⟩)) = _
    cases G.ports ⟨ve.symm v,i⟩ <;> rfl
  · apply Fintype.prod_equiv ee.symm
    intro e
    simp [graph]

omit [Fintype V] [Fintype E] in
theorem graph_nativeX (hG : ∀ e,G.edge e = Signature.disequality) :
    (graph G ve ee).NativeX := fun e => hG (ee.symm e)

omit [Fintype V] [Fintype E] [CommSemiring K] in
theorem graph_uses (F : SignatureFamily K)
    (hG : ∀ v,(⟨G.arity v,G.vertex v⟩ : AnySignature K) ∈ F) :
    (graph G ve ee).Uses F := fun v => hG (ve.symm v)

end
end Paper2.DegreeCSP.OrderedEnumeration
