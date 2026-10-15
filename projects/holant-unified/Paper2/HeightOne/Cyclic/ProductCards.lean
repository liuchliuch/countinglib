import Paper2.HeightOne.Cyclic.ActualDeck
import Paper2.HeightOne.PhaseCards.ProductRectangles

/-! The actual minimum-prime cards retain coefficient factorization, in
addition to their matching support. This is needed by the polynomial minors. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable ExactInput GroupSplit GroupSplit.MatrixGroup PhaseCards EndpointSelfLoop

/-- Minimum arity and the full actual group put every chosen card in Product
in the one fixed Walsh coordinate system. -/
theorem minimum_card_walsh_product {F : SignatureFamily AlgebraicComplex}
    (M : BinaryMenu F) (L : Language) (heven : ∀ f ∈ L.family, Even f.1)
    (hsafe : AllBinariesSafe L.family) {N n : ℕ}
    (hG : actualClasses L.family = cyclicPhaseClasses N ∨ actualClasses L.family = dihedralPhaseClasses N)
    (hmin : LeastPrimeArity L.family n)
    (f : AnySignature AlgebraicComplex) (hf : f.1 = n) (hprocessed : M.Processed f L)
    (k : M.Choices f) (hcard : 0 < (M.produced f k).1 ∧ (M.produced f k).2 ≠ 0) :
    Product (walshCoordinates (M.produced f k).2) := by
  let Q := selectedDecomposition (M.produced f k) hcard
  have hQ := selectedDecomposition_spec (M.produced f k) hcard
  have hc (i : Fin Q.count) : (⟨Q.arity i, Q.factor i⟩ : AnySignature AlgebraicComplex) ∈ M.children f := by
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [selectedFactors, dif_pos hcard]
    exact ⟨i, rfl⟩
  have hmem := fun i => hprocessed.2.1 (hc i)
  have htwo : ∀ i, Q.arity i = 2 := fun i =>
    selected_card_factors_binary M L heven hmin f hf hprocessed (hc i)
  have hp := Product.decomposition (Q.mapAction walshInv) (fun i => by
    have h := normalized_signature_product hG hsafe (Q.factor i) (htwo i)
      (networkRealizable_of_mem (hmem i)) (hQ.2.2 i).1
    simpa only [TensorDecomposition.mapAction, ← walshCoordinates_eq_coordinateAction] using h)
  have he := (TensorDecomposition.value_mapAction Q walshInv).trans
    (walshCoordinates_eq_coordinateAction Q.value).symm
  rw [he, hQ.1] at hp
  exact hp

variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]

lemma rotation_walsh_produced (C : RotationCards F N) {n : ℕ} (f : Signature AlgebraicComplex n)
    (a b : Fin n) (hab : a ≠ b) (s : rootsOfUnity N AlgebraicComplex) :
    walshCoordinates ((rotationMenu C).produced ⟨n, f⟩ (rotationChoice C f a b hab s)).2 =
      (2 * C.scale s) • Tensor.reindex (Fintype.equivFin (Remaining a b))
        (plusContraction a b hab (s.val : AlgebraicComplex) (walshCoordinates f)) := by
  simp only [BinaryMenu.produced, rotationChoice, BinaryMenu.oriented, rotationMenu,
    Bool.false_eq_true, if_false, Equiv.symm_apply_apply]
  rw [walshCoordinates_reindex]
  change Tensor.reindex (Fintype.equivFin (Remaining a b))
    (walshCoordinates (C.contraction a b hab s f)) = _
  rw [C.walsh]
  rfl

/-- Analytic plus-card Product factorization is proved by dividing the exact
nonzero Walsh scale; division is not asserted to be a gadget operation. -/
theorem minimum_plusCard_product (C : RotationCards F N) (L : Language)
    (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hG : actualClasses L.family = cyclicPhaseClasses N ∨ actualClasses L.family = dihedralPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n)
    (hprocessed : (rotationMenu C).Processed ⟨n, f⟩ L)
    (a b : Fin n) (hab : a ≠ b) (s : rootsOfUnity N AlgebraicComplex) :
    Product (Tensor.reindex (Fintype.equivFin (Remaining a b))
      (plusContraction a b hab (s.val : AlgebraicComplex) (walshCoordinates f))) := by
  classical
  let k := rotationChoice C f a b hab s
  let g := (rotationMenu C).produced ⟨n, f⟩ k
  have hwalsh := rotation_walsh_produced C f a b hab s
  change walshCoordinates g.2 = _ at hwalsh
  by_cases hgn : g.2 = 0
  · apply Or.inl
    rw [hgn, walsh_zero] at hwalsh
    funext x
    have h := congrFun hwalsh x
    exact (mul_eq_zero.mp h.symm).resolve_left (C.walsh_scale_ne_zero s)
  have hp : 0 < g.1 := by
    have harity := (rotationMenu C).produced_arity ⟨n, f⟩ k
    have hmin3 := hmin.ge_three
    change g.1 + 2 = n at harity
    omega
  have hprod := minimum_card_walsh_product (rotationMenu C) L heven hsafe hG hmin
    ⟨n, f⟩ rfl hprocessed k ⟨hp, hgn⟩
  rw [hwalsh] at hprod
  have hs := hprod.scale (2 * C.scale s)⁻¹
  simpa only [Pi.smul_apply, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (C.walsh_scale_ne_zero s), one_mul] using hs

end
end Paper2.HeightOne.Cyclic
