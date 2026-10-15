import Paper2.HeightOne.PhaseCards.FieldGroup
import Paper2.Tractable.Conformal.Shape

/-! Exact actual-gadget and fixed-field transport for every algebraic GO(X)
kernel. Both diagonal and antidiagonal kernels retain the original incidence
bijection. The internal-edge multiplier is kept and proved nonzero. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.GroupSplit
open Tractable Tractable.Conformal MatrixGroup
noncomputable section

namespace Network

/-- The same ordered graph, with one shared kernel applied at every vertex. -/
abbrev conformalTransform {n : ℕ} (G : Paper2.Network AlgebraicComplex n)
    (D : InvertibleKernel) := diagonalTransform G D

theorem denote_conformalTransform_shape {n : ℕ} (G : Paper2.Network AlgebraicComplex n)
    (D : InvertibleKernel) (opposite : Bool) (a b : AlgebraicComplex)
    (hD : HasShape D opposite a b) (hG : G.NativeX) :
    (conformalTransform G D).denote =
      ((a * b) ^ G.shape.edges) • D.action G.denote := by
  let localWord := fun (x : Fin n → Bool) (z : Fin G.shape.edges → Bool)
      (v : Fin G.shape.vertices) (i : Fin (G.shape.arity v)) =>
    Sum.elim x (fun p : Fin G.shape.edges × Bool =>
      if p.2 then !(z p.1) else z p.1) (G.shape.ports ⟨v, i⟩)
  have hflip (x : Fin n → Bool) (z : Fin G.shape.edges → Bool)
      (v : Fin G.shape.vertices) :
      flipWord opposite (localWord x z v) =
        localWord (flipWord opposite x) (flipWord opposite z) v := by
    cases opposite
    · rfl
    · funext i
      dsimp [flipWord, complementWord, localWord]
      cases G.shape.ports ⟨v, i⟩ with
      | inl j => rfl
      | inr p => rcases p with ⟨j, t⟩; cases t <;> simp
  let e : (Fin G.shape.edges → Bool) ≃ (Fin G.shape.edges → Bool) :=
    ⟨flipWord opposite, flipWord opposite, flipWord_twice opposite,
      flipWord_twice opposite⟩
  have hsum (x : Fin n → Bool) :
      (∑ z : Fin G.shape.edges → Bool,
        ∏ v, G.vertex v (flipWord opposite (localWord x z v))) =
      ∑ z : Fin G.shape.edges → Bool,
        ∏ v, G.vertex v (localWord (flipWord opposite x) z v) := by
    apply Fintype.sum_equiv e
    intro z
    apply Finset.prod_congr rfl
    intro v _
    rw [hflip]
    rfl
  funext x
  rw [Paper2.Network.denote_nativeX _ (diagonalTransform_nativeX G D hG)]
  have hact (m : ℕ) (f : Signature AlgebraicComplex m) :
      D.action f = fun y => diagonalCoefficient a b y * f (flipWord opposite y) :=
    shape_action hD f
  simp only [diagonalTransform, hact, Finset.prod_mul_distrib,
    diagonal_coefficients, Pi.smul_apply, smul_eq_mul]
  change (∑ z : Fin G.shape.edges → Bool,
    (diagonalCoefficient a b x * (a * b) ^ G.shape.edges) *
      ∏ v, G.vertex v (flipWord opposite (localWord x z v))) = _
  rw [← Finset.mul_sum, hsum]
  rw [Paper2.Network.denote_nativeX G hG]
  change (diagonalCoefficient a b x * (a * b) ^ G.shape.edges) * _ =
    (a * b) ^ G.shape.edges * (diagonalCoefficient a b x * _)
  ring

end Network

/-- Every actual gadget remains an actual gadget after an arbitrary conformal
normalization, with its nonzero graph-derived scalar explicitly retained. -/
theorem realizable_conformal_transport {F : SignatureFamily AlgebraicComplex}
    {n : ℕ} {f : Signature AlgebraicComplex n} (hf : NetworkRealizable F f)
    (D : InvertibleKernel) (hD : XConformal D) :
    ∃ c : AlgebraicComplex, c ≠ 0 ∧
      NetworkRealizable (familyAction D F) (c • D.action f) := by
  obtain ⟨opposite, a, b, ha, hb, hshape⟩ := hasShape_of_xConformal hD
  obtain ⟨G, hU, hX, hden⟩ := hf.ordered
  refine ⟨(a * b) ^ G.shape.edges, pow_ne_zero _ (mul_ne_zero ha hb),
    n, Network.conformalTransform G D, Equiv.refl _,
    Network.diagonalTransform_uses G D hU,
    Network.diagonalTransform_nativeX G D hX, ?_⟩
  simp only [Tensor.reindex_refl,
    Network.denote_conformalTransform_shape G D opposite a b hshape hX, hden]

lemma ActualNonsingular.conformal_transport {F : SignatureFamily AlgebraicComplex}
    {B : AMat} (hB : ActualNonsingular F B)
    (D : InvertibleKernel) (hD : XConformal D) :
    ∃ B' : AMat, ActualNonsingular (familyAction D F) B' ∧
      ∃ c : AlgebraicComplex, c ≠ 0 ∧
        transfer B' = c • ((Matrix.of D.matrix) * transfer B * (Matrix.of D.inverse)) := by
  obtain ⟨c, hc, hreal⟩ := realizable_conformal_transport hB.1 D hD
  obtain ⟨d, hd, hpull⟩ := hD
  let B' : AMat := c • ((Matrix.of D.matrix) * B * (Matrix.of D.matrix).transpose)
  have hreal' : NetworkRealizable (familyAction D F) (binarySignature B') := by
    rw [binary_action_matrix] at hreal
    exact hreal
  have hdetD : Matrix.det (Matrix.of D.matrix) ≠ 0 :=
    Matrix.GeneralLinearGroup.det_ne_zero (basisGL D)
  refine ⟨B', ⟨hreal', ?_⟩, c * d, mul_ne_zero hc hd, ?_⟩
  · dsimp [B']
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hc) (mul_ne_zero (mul_ne_zero hdetD hB.2) hdetD)
  · dsimp [B']
    rw [transfer, Matrix.smul_mul]
    change c • transfer ((Matrix.of D.matrix) * B * (Matrix.of D.matrix).transpose) = _
    rw [conformal_transfer D d hpull, smul_smul]

lemma actualClasses_conformal_forward {F : SignatureFamily AlgebraicComplex}
    (D : InvertibleKernel) (hD : XConformal D)
    {q : PGL2 AlgebraicComplex} (hq : q ∈ actualClasses F) :
    pglMk _ (basisGL D) * q * (pglMk _ (basisGL D))⁻¹ ∈
      actualClasses (familyAction D F) := by
  obtain ⟨U, ⟨B, hB, t, ht, hU⟩, rfl⟩ := hq
  obtain ⟨B', hB', c, hc, he⟩ := hB.conformal_transport D hD
  let V := basisGL D * U * (basisGL D)⁻¹
  refine ⟨V, ⟨B', hB', t / c, div_ne_zero ht hc, ?_⟩, ?_⟩
  · change (Matrix.of D.matrix) * (U : AMat) * (Matrix.of D.inverse) =
      (t / c) • transfer B'
    rw [hU, Matrix.mul_smul, Matrix.smul_mul, he, smul_smul]
    rw [div_mul_cancel₀ _ hc]
  · simp only [V, map_mul, map_inv]

/-- Exact equality of complete actual transfer sets, with both directions
proved by the same actual graph transport. No nonempty-group premise is needed. -/
theorem completeClasses_conformal_transport (F : SignatureFamily AlgebraicComplex)
    (D : InvertibleKernel) (hD : XConformal D) :
    actualClasses (familyAction D F) =
      (fun q => pglMk _ (basisGL D) * q * (pglMk _ (basisGL D))⁻¹) '' actualClasses F := by
  ext q
  constructor
  · intro hq
    have hp := actualClasses_conformal_forward D.symm hD.symm hq
    have hp' : (pglMk _ (basisGL D))⁻¹ * q * pglMk _ (basisGL D) ∈ actualClasses F := by
      simpa only [basisGL_symm, map_inv, inv_inv, Conformal.familyAction_symm_action] using hp
    refine ⟨_, hp', ?_⟩
    group
  · rintro ⟨q, hq, rfl⟩
    exact actualClasses_conformal_forward D hD hq

/-- Retaining more original vertex labels preserves each literal actual
transfer witness, with no synthesis or group closure assumption. -/
theorem actualClasses_mono {F G : SignatureFamily AlgebraicComplex} (hFG : F ⊆ G) :
    actualClasses F ⊆ actualClasses G := by
  rintro q ⟨U, ⟨B, ⟨hf, hd⟩, c, hc, hU⟩, rfl⟩
  refine ⟨U, ⟨B, ⟨?_, hd⟩, c, hc, hU⟩, rfl⟩
  obtain ⟨n, N, e, huses, hX, hden⟩ := hf
  exact ⟨n, N, e, fun v => hFG (huses v), hX, hden⟩

end
end Paper2.HeightOne.GroupSplit

namespace Paper2.HeightOne.PhaseCards
open Tractable GroupSplit GroupSplit.MatrixGroup
noncomputable section

/-- Inverse conformal graph transport cancels any legal ledger coordinate,
including antidiagonal coordinates, before applying the frozen field invariant. -/
theorem network_pullbackOver_conformal (E : Subfield AlgebraicComplex)
    (A : InvertibleKernel) (hA : XConformal A)
    {F : SignatureFamily AlgebraicComplex} (hF : ∀ f ∈ F, PullbackOver E A f)
    {n : ℕ} {f : Signature AlgebraicComplex n} (hf : NetworkRealizable F f) :
    PullbackOver E A ⟨n, f⟩ := by
  obtain ⟨c, hc, hreal⟩ := realizable_conformal_transport hf A.symm hA.symm
  have hf' : ∀ g ∈ familyAction A.symm F, ProjectivelyOver E g.2 := by
    rintro g ⟨f, hf, rfl⟩
    exact hF f hf
  have h := network_projectivelyOver E hf' hreal
  have hh := h.scale (inv_ne_zero hc)
  simpa only [PullbackOver, smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

/-- All actual transfers pulled back through an arbitrary ledger GO(X) basis
lie in the literal image of PGL₂ of the one fixed original field. -/
theorem pulledback_actualClasses_conformal_in_subfield_range (E : Subfield AlgebraicComplex)
    (A : InvertibleKernel) (hA : XConformal A)
    {F : SignatureFamily AlgebraicComplex} (hF : ∀ f ∈ F, PullbackOver E A f) :
    (fun q => (pglMk _ (basisGL A))⁻¹ * q * pglMk _ (basisGL A)) '' actualClasses F ⊆
      (pglMap E.subtype).range := by
  have hfield : ∀ f ∈ familyAction A.symm F, ProjectivelyOver E f.2 := by
    rintro f ⟨g, hg, rfl⟩
    exact hF g hg
  have h := actualClasses_in_subfield_range E hfield
  rw [completeClasses_conformal_transport F A.symm hA.symm] at h
  simpa only [basisGL_symm, map_inv, inv_inv] using h


end
end Paper2.HeightOne.PhaseCards
