import Paper2.Paper1ProvedGadgetController

/-! Literal ordered network and resource-label translation into the actual
Paper 1 fixed-template compiler. Every vertex, edge, and boundary incidence
is copied; the two finite denotations agree definitionally. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput
open Holant.Complexity.FixedGadgetSubstitution
noncomputable section
set_option backward.isDefEq.respectTransparency false

def sourceShape {n : ℕ} (S : Paper2.NetworkShape n) : Holant.NetworkShape n :=
  ⟨S.vertices,S.arity,S.edges,S.ports⟩

def sourceNetwork {K : Type} {n : ℕ} (N : Paper2.Network K n) : Holant.Network K n :=
  ⟨sourceShape N.shape,N.vertex,N.edge⟩

@[simp] theorem sourceNetwork_denote {K : Type} [CommSemiring K] {n : ℕ}
    (N : Paper2.Network K n) : (sourceNetwork N).denote = N.denote := rfl

def vertexLabel (L : Language) {n : ℕ} (N : Paper2.Network AlgebraicComplex n)
    (h : N.Uses L.family) (v : Fin N.shape.vertices) : Fin L.count :=
  Classical.choose (h v)

theorem vertexLabel_literal (L : Language) {n : ℕ} (N : Paper2.Network AlgebraicComplex n)
    (h : N.Uses L.family) (v : Fin N.shape.vertices) :
    (⟨L.arity (vertexLabel L N h v).val,L.signature (vertexLabel L N h v)⟩ :
      AnySignature AlgebraicComplex) = ⟨N.shape.arity v,N.vertex v⟩ :=
  Classical.choose_spec (h v)

def sourceLabels (L : Language) {n : ℕ} (N : Paper2.Network AlgebraicComplex n)
    (h : N.Uses L.family) : Labelling (sourceShape N.shape) L.count 1 L.arity where
  vertex := vertexLabel L N h
  vertex_arity v := congrArg Sigma.fst (vertexLabel_literal L N h v)
  edge _ := 0

 theorem labelled_denote (L : Language) {n : ℕ} (N : Paper2.Network AlgebraicComplex n)
    (h : N.Uses L.family) (hX : N.NativeX) :
    ((sourceLabels L N h).template.network (sourceLabels L N h).wellFormed
      (signatures L) (kernels .nativeX)).denote = N.denote := by
  rw [← sourceNetwork_denote N]
  apply Labelling.denote_template_of_labels
  · intro v x
    have hl := vertexLabel_literal L N h v
    have ha := congrArg Sigma.fst hl
    exact Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
      (L.signature (vertexLabel L N h v)) (N.vertex v) hl ha x
  · intro e a b
    exact (congrFun (congrFun (hX e) a) b).symm

end
end Paper2.Paper1Proved
