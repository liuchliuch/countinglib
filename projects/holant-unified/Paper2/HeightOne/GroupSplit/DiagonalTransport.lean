import Paper2.HeightTwo.Normalization
import Paper2.NetworkSubstitution

/-! Actual-graph diagonal transport, preserving all vertices and edges. The
nonzero multiplier is exactly one diagonal determinant per internal X edge. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.GroupSplit
open Tractable
noncomputable section

namespace Network
variable {n : ℕ}

def diagonalTransform (G : Paper2.Network AlgebraicComplex n) (D : InvertibleKernel) :
    Paper2.Network AlgebraicComplex n where
  shape := G.shape
  vertex := fun v => D.action (G.vertex v)
  edge := G.edge

lemma diagonalTransform_uses (G : Paper2.Network AlgebraicComplex n)
    (D : InvertibleKernel) {F : SignatureFamily AlgebraicComplex} (hG : G.Uses F) :
    (diagonalTransform G D).Uses (familyAction D F) := by
  intro v
  exact ⟨⟨G.shape.arity v, G.vertex v⟩, hG v, rfl⟩

lemma diagonalTransform_nativeX (G : Paper2.Network AlgebraicComplex n)
    (D : InvertibleKernel) (hG : G.NativeX) : (diagonalTransform G D).NativeX := hG

/-- Incidence bijectivity counts every exposed occurrence once and every
internal edge twice, with complementary bits at its two ordered ends. -/
lemma diagonal_coefficients (s : NetworkShape n) (a b : AlgebraicComplex)
    (x : Fin n → Bool) (z : Fin s.edges → Bool) :
    (∏ v, diagonalCoefficient a b
      (fun i => Sum.elim x
        (fun p : Fin s.edges × Bool => if p.2 then !(z p.1) else z p.1)
        (s.ports ⟨v, i⟩))) =
      diagonalCoefficient a b x * (a * b) ^ s.edges := by
  let w : (Fin n ⊕ (Fin s.edges × Bool)) → Bool :=
    Sum.elim x (fun p => if p.2 then !(z p.1) else z p.1)
  change (∏ v, ∏ i, if w (s.ports ⟨v, i⟩) then b else a) = _
  rw [← Fintype.prod_sigma (fun p => if w (s.ports p) then b else a)]
  rw [s.ports.prod_comp (fun p => if w p then b else a)]
  rw [Fintype.prod_sum_type]
  change diagonalCoefficient a b x *
    (∏ p : Fin s.edges × Bool, if (if p.2 then !(z p.1) else z p.1) then b else a) = _
  congr 1
  rw [Fintype.prod_prod_type]
  have he : ∀ e : Fin s.edges,
      (∏ t : Bool, if (if t then !(z e) else z e) then b else a) = a * b := by
    intro e
    cases hz : z e <;> simp [hz, mul_comm]
  simp only [he, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- Exact boundary identity for the actual network denotation. -/
theorem denote_diagonalTransform (G : Paper2.Network AlgebraicComplex n)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (hG : G.NativeX) :
    (diagonalTransform G D).denote =
      ((a * b) ^ G.shape.edges) • D.action G.denote := by
  funext x
  rw [Paper2.Network.denote_nativeX _ (diagonalTransform_nativeX G D hG)]
  have hact (m : ℕ) (f : Signature AlgebraicComplex m) :
      D.action f = fun y => diagonalCoefficient a b y * f y := by
    unfold InvertibleKernel.action
    rw [hD]
    exact coordinateAction_diagonal a b f
  simp only [diagonalTransform, hact, Finset.prod_mul_distrib,
    diagonal_coefficients, Pi.smul_apply, smul_eq_mul]
  rw [Paper2.Network.denote_nativeX G hG]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

end Network

/-- A legal diagonal global basis transports every actual gadget. The scalar
is supplied by its graph and is proved nonzero, rather than erased. -/
theorem realizable_diagonal_transport {F : SignatureFamily AlgebraicComplex}
    {n : ℕ} {f : Signature AlgebraicComplex n} (hf : NetworkRealizable F f)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ c : AlgebraicComplex, c ≠ 0 ∧
      NetworkRealizable (familyAction D F) (c • D.action f) := by
  obtain ⟨G, hU, hX, hden⟩ := hf.ordered
  refine ⟨(a * b) ^ G.shape.edges, pow_ne_zero _ (mul_ne_zero ha hb),
    n, Network.diagonalTransform G D, Equiv.refl _,
    Network.diagonalTransform_uses G D hU,
    Network.diagonalTransform_nativeX G D hX, ?_⟩
  simp only [Tensor.reindex_refl, Network.denote_diagonalTransform G D a b hD hX, hden]

end
end Paper2.HeightOne.GroupSplit
