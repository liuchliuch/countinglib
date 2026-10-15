import Paper2.GadgetTrace
import Paper2.NetworkRealization

/-!
# Native-X vertex substitution in actual networks

Substitution retains all inner vertices and edges and all outer edges. Its
incidence bijection identifies each replacement's boundary with the original
ordered local ports. The denotation theorem is a finite-sum Fubini identity.
-/

set_option backward.isDefEq.respectTransparency false

namespace Paper2

open scoped BigOperators Classical

namespace Network

variable {K : Type*} {n : ℕ}

/-- The finite-index presentation of an existing ordinary network. -/
def toFiniteModel (G : Network K n) :
    FiniteNetwork K (Fin G.shape.vertices) (Fin G.shape.edges) n where
  arity := G.shape.arity
  ports := G.shape.ports
  vertex := G.vertex
  edge := G.edge

theorem denote_toFiniteModel [CommSemiring K] (G : Network K n) :
    G.toFiniteModel.denote = G.denote := by
  classical
  funext x
  unfold FiniteNetwork.denote denote
  refine Finset.sum_congr (by ext; simp) ?_
  intro z _
  rfl

/-- Native-X normalization of the original `Network.denote`. -/
theorem denote_nativeX [CommSemiring K] (G : Network K n)
    (hX : ∀ e, G.edge e = Signature.disequality) (x : Fin n → Bool) :
    G.denote x = ∑ z : Fin G.shape.edges → Bool,
      ∏ v, G.vertex v (fun i => Sum.elim x
        (fun q : Fin G.shape.edges × Bool => if q.2 then !(z q.1) else z q.1)
          (G.shape.ports ⟨v, i⟩)) := by
  rw [← denote_toFiniteModel]
  refine (FiniteNetwork.denote_nativeX G.toFiniteModel hX x).trans ?_
  refine Finset.sum_congr (by ext; simp) ?_
  intro z _
  rfl

/-- All replacement vertices, with the outer occurrence retained. -/
abbrev SubVertices (G : Network K n)
    (R : (v : Fin G.shape.vertices) → Network K (G.shape.arity v)) :=
  Σ v : Fin G.shape.vertices, Fin (R v).shape.vertices

/-- All replacement-internal edges, separately indexed by their outer vertex. -/
abbrev SubInnerEdges (G : Network K n)
    (R : (v : Fin G.shape.vertices) → Network K (G.shape.arity v)) :=
  Σ v : Fin G.shape.vertices, Fin (R v).shape.edges

abbrev SubEdges (G : Network K n)
    (R : (v : Fin G.shape.vertices) → Network K (G.shape.arity v)) :=
  Fin G.shape.edges ⊕ SubInnerEdges G R

/-- The new graph before enumerating its vertices and edges by `Fin`. -/
def substituteFinite (G : Network K n)
    (R : (v : Fin G.shape.vertices) → Network K (G.shape.arity v)) :
    FiniteNetwork K (SubVertices G R) (SubEdges G R) n where
  arity := fun p => (R p.1).shape.arity p.2
  ports := (Equiv.sigmaAssoc (fun v w => Fin ((R v).shape.arity w))).trans
    ((Equiv.sigmaCongrRight (fun v => (R v).shape.ports)).trans
      ((Equiv.sigmaSumDistrib (fun v => Fin (G.shape.arity v))
          (fun v => Fin (R v).shape.edges × Bool)).trans
        ((Equiv.sumCongr G.shape.ports
            (Equiv.sigmaProdDistrib (fun v => Fin (R v).shape.edges) Bool).symm).trans
          ((Equiv.sumAssoc _ _ _).trans
            (Equiv.sumCongr (Equiv.refl _)
              (Equiv.sumProdDistrib (Fin G.shape.edges) (SubInnerEdges G R) Bool).symm)))))
  vertex := fun p => (R p.1).vertex p.2
  edge := Sum.elim G.edge (fun p => (R p.1).edge p.2)

/-- Literal substitution, now in the original ordered-port Network model. -/
noncomputable def substitute (G : Network K n)
    (R : (v : Fin G.shape.vertices) → Network K (G.shape.arity v)) : Network K n :=
  (G.substituteFinite R).toNetwork

/-- The new native edge word consists of the outer word and one independent
native word for each replacement graph. -/
def substitutionAssignments (G : Network K n)
    (R : (v : Fin G.shape.vertices) → Network K (G.shape.arity v)) :
    (SubEdges G R → Bool) ≃
      ((Fin G.shape.edges → Bool) × ((v : Fin G.shape.vertices) → Fin (R v).shape.edges → Bool)) where
  toFun z := (fun e => z (.inl e), fun v e => z (.inr ⟨v, e⟩))
  invFun p := Sum.elim p.1 (fun q => p.2 q.1 q.2)
  left_inv := by intro z; funext e; rcases e with e | ⟨v, e⟩ <;> rfl
  right_inv := by intro p; rfl

/-- Native-X labels are inherited literally by all old and replacement edges. -/
theorem substituteFinite_nativeX [CommSemiring K] (G : Network K n)
    (R : (v : Fin G.shape.vertices) → Network K (G.shape.arity v))
    (hG : ∀ e, G.edge e = Signature.disequality)
    (hR : ∀ v e, (R v).edge e = Signature.disequality) :
    ∀ e, (G.substituteFinite R).edge e = Signature.disequality := by
  rintro (e | ⟨v, e⟩)
  · exact hG e
  · exact hR v e

/-- Exact coefficient identity for replacement of every vertex by a network.
No new scalar, approximation, or postulated gadget-denotation law is used. -/
theorem denote_substituteFinite [CommSemiring K] (G : Network K n)
    (R : (v : Fin G.shape.vertices) → Network K (G.shape.arity v))
    (hG : ∀ e, G.edge e = Signature.disequality)
    (hR : ∀ v e, (R v).edge e = Signature.disequality)
    (hden : ∀ v, (R v).denote = G.vertex v) :
    (G.substituteFinite R).denote = G.denote := by
  classical
  letI : DecidableEq (SubEdges G R) := Classical.decEq _
  funext x
  rw [FiniteNetwork.denote_nativeX _ (G.substituteFinite_nativeX R hG hR)]
  rw [← (substitutionAssignments G R).symm.sum_comp]
  rw [G.denote_nativeX hG x]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr (by ext; simp) ?_
  intro z _
  have hlocal : ∀ v, G.vertex v (fun i => Sum.elim x
        (fun q : Fin G.shape.edges × Bool => if q.2 then !(z q.1) else z q.1)
        (G.shape.ports ⟨v, i⟩)) =
      ∑ w : Fin (R v).shape.edges → Bool,
        ∏ u, (R v).vertex u (fun j => Sum.elim
          (fun i => Sum.elim x
            (fun q : Fin G.shape.edges × Bool => if q.2 then !(z q.1) else z q.1)
            (G.shape.ports ⟨v, i⟩))
          (fun q : Fin (R v).shape.edges × Bool => if q.2 then !(w q.1) else w q.1)
          ((R v).shape.ports ⟨u, j⟩)) := by
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
  dsimp [substituteFinite, substitutionAssignments, Equiv.sigmaAssoc,
    Equiv.sigmaCongrRight]
  generalize hr : (R v).shape.ports ⟨u, j⟩ = q
  cases q with
  | inl i =>
    generalize hg : G.shape.ports ⟨v, i⟩ = p
    cases p <;> simp_all [Equiv.sigmaSumDistrib, Equiv.sumCongr, Equiv.sumAssoc, Equiv.sumProdDistrib, Equiv.sigmaProdDistrib]
  | inr q => simp_all [Equiv.sigmaSumDistrib, Equiv.sumCongr, Equiv.sumAssoc, Equiv.sumProdDistrib, Equiv.sigmaProdDistrib]

/-- Substitution preserves the original, fully expanded sum-product denotation. -/
theorem denote_substitute [CommSemiring K] (G : Network K n)
    (R : (v : Fin G.shape.vertices) → Network K (G.shape.arity v))
    (hG : ∀ e, G.edge e = Signature.disequality)
    (hR : ∀ v e, (R v).edge e = Signature.disequality)
    (hden : ∀ v, (R v).denote = G.vertex v) :
    (G.substitute R).denote = G.denote := by
  rw [substitute, FiniteNetwork.denote_toNetwork]
  exact G.denote_substituteFinite R hG hR hden

/-- Vertex-resource membership is inherited from the replacement networks;
none of the outer supplied labels remain as new resource assumptions. -/
theorem substitute_uses (G : Network K n)
    (R : (v : Fin G.shape.vertices) → Network K (G.shape.arity v))
    {F : SignatureFamily K} (hR : ∀ v, (R v).Uses F) :
    (G.substitute R).Uses F := by
  intro w
  exact hR ((Fintype.equivFin (SubVertices G R)).symm w).1
    ((Fintype.equivFin (SubVertices G R)).symm w).2

theorem substitute_nativeX [CommSemiring K] (G : Network K n)
    (R : (v : Fin G.shape.vertices) → Network K (G.shape.arity v))
    (hG : G.NativeX) (hR : ∀ v, (R v).NativeX) :
    (G.substitute R).NativeX := by
  intro e
  exact G.substituteFinite_nativeX R hG hR
    ((Fintype.equivFin (SubEdges G R)).symm e)

end Network

namespace NetworkRealizable

variable {K : Type} [CommSemiring K] {F : SignatureFamily K} {n : ℕ}

/-- Compile every supplied vertex of an outer native-X network to an actual
network over F, then inline the graphs with the proved substitution constructor. -/
theorem substitute (G : Network K n) (hG : G.NativeX)
    (hv : ∀ v, NetworkRealizable F (G.vertex v)) : NetworkRealizable F G.denote := by
  classical
  have h : ∀ v, ∃ R : Network K (G.shape.arity v),
      R.Uses F ∧ R.NativeX ∧ R.denote = G.vertex v := fun v => (hv v).ordered
  choose R hU hX hd using h
  refine ⟨n, G.substitute R, Equiv.refl _, G.substitute_uses R hU,
    G.substitute_nativeX R hG hX, ?_⟩
  simp only [Tensor.reindex_refl]
  exact G.denote_substitute R hG hX hd

/-- Actual graph realizability is transitive through any intermediate resource
family, with its witnesses inlined rather than treated as primitive vertices. -/
theorem trans {H : SignatureFamily K} {ι : Type} {f : Tensor K ι}
    (h : NetworkRealizable H f)
    (hH : ∀ g ∈ H, NetworkRealizable F g.2) : NetworkRealizable F f := by
  obtain ⟨n, G, e, hU, hX, he⟩ := h
  have hg : NetworkRealizable F G.denote := substitute G hX (fun v => hH _ (hU v))
  exact he ▸ hg.reindex e

end NetworkRealizable

namespace MountainConstruction

variable {K : Type} [CommSemiring K] {F : SignatureFamily K} {d : ℕ}

/-- Every connector menu entry has a real network over the original resources,
provided the two endpoint tables have such networks. This theorem actually
substitutes the endpoint implementations into its two/three supplied vertices. -/
theorem PairGadget.networkRealizable {P N M : Tensor K (Fin d ⊕ Fin d)}
    (h : PairGadget P N M) (hP : NetworkRealizable F P) (hN : NetworkRealizable F N) :
    NetworkRealizable F M := by
  obtain ⟨G, hU, hX, he⟩ := h.realized
  have hP' := hP.reindex (blockEquiv d)
  have hN' := hN.reindex (blockEquiv d)
  have hv : ∀ v, NetworkRealizable F (G.vertex v) := by
    intro v
    rcases hU v with hp | hn
    · exact Eq.mpr (congrArg (fun g : AnySignature K => NetworkRealizable F g.2) hp) hP'
    · exact Eq.mpr (congrArg (fun g : AnySignature K => NetworkRealizable F g.2) hn) hN'
  have hg := NetworkRealizable.substitute G hX hv
  have hm : NetworkRealizable F (Tensor.reindex (blockEquiv d) M) := he ▸ hg
  have hout := hm.reindex (blockEquiv d).symm
  simpa only [Tensor.reindex_symm] using hout

/-- The full post-endpoint alternative with a source-labelled graph over F. -/
theorem networkRealizable_mountain_or_pure [NoZeroDivisors K]
    {P N : Tensor K (Fin d ⊕ Fin d)} (hd : 0 < d)
    (hPone : P (fun _ => true) ≠ 0) (hNzero : N (fun _ => false) ≠ 0)
    (hPd : Tensor.HalfChargeDivisible P d) (hNd : Tensor.HalfChargeDivisible N d)
    (hP : NetworkRealizable F P) (hN : NetworkRealizable F N) :
    (∃ M : Signature K (2 * d), IsMountain M ∧ NetworkRealizable F M) ∨
      (P = onePointMass (P (fun _ => true)) ∧
        N = zeroPointMass (N (fun _ => false))) := by
  rcases endpoint_pair_mountain_or_pure_of_divisible hd hPone hNzero hPd hNd with
    ⟨M, hM, hm⟩ | hpure
  · exact Or.inl ⟨_, hm, (hM.networkRealizable hP hN).reindex (blockEquiv d)⟩
  · exact Or.inr hpure

end MountainConstruction
end Paper2

