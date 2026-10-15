import Paper2.HeightOne.Cyclic.LogicalSlices

/-! Apply only the exact complex Lemma 7.8, then descend its unary parameters
by their explicit singleton coefficient values. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable
open scoped BigOperators

lemma unaryDiagonals_complex {r : ℕ} (h : Signature AlgebraicComplex r)
    (hd : DiagonalSlices.UnaryDiagonals h) :
    DiagonalSlices.UnaryDiagonals (fun t => (h t : ℂ)) := by
  intro i j hij
  obtain ⟨c, u, hc, hu, he⟩ := hd i j hij
  refine ⟨(c : ℂ), fun k b => (u k b : ℂ), ?_, ?_, ?_⟩
  · exact_mod_cast hc
  · intro k b
    change (u k b : ℂ) ≠ 0
    exact_mod_cast hu k b
  · intro t ht
    change (h t : ℂ) = (c : ℂ) * ∏ k, (u k (t k) : ℂ)
    exact_mod_cast he t ht

lemma unaryDiagonals_scale {r : ℕ} (h : Signature AlgebraicComplex r)
    (hd : DiagonalSlices.UnaryDiagonals h) (c : AlgebraicComplex) (hc : c ≠ 0) :
    DiagonalSlices.UnaryDiagonals (fun t => c * h t) := by
  intro i j hij
  obtain ⟨a, u, ha, hu, he⟩ := hd i j hij
  exact ⟨c * a, u, mul_ne_zero hc ha, hu, fun t ht => by change c * h t = _; rw [he t ht]; ring⟩

/-- Algebraic unary witnesses are the actual singleton entries. Their
algebraicity is proved here, not silently strengthened in the Paper 1 input. -/
theorem diagonal_large_algebraic (P1 : Paper1DiagonalSlicesAccepted)
    {r : ℕ} (hr : 4 ≤ r) (h : Signature AlgebraicComplex r)
    (hfull : ∀ t, h t ≠ 0) (h0 : h (fun _ => false) = 1)
    (hd : DiagonalSlices.UnaryDiagonals h) :
    ∃ ρ : Fin r → AlgebraicComplex, (∀ i, ρ i ≠ 0) ∧
      ∀ t, h t = ∏ i, (if t i then ρ i else 1) := by
  obtain ⟨ρ, hρ, he⟩ := P1.diagonal_large_7_8 r hr (fun t => (h t : ℂ))
    (fun t => by exact_mod_cast hfull t) (by exact_mod_cast h0) (unaryDiagonals_complex h hd)
  have hρval (i : Fin r) : (h (DiagonalSlices.singleWord i) : ℂ) = ρ i := by
    simpa [DiagonalSlices.singleWord] using he (DiagonalSlices.singleWord i)
  refine ⟨fun i => h (DiagonalSlices.singleWord i), fun i => hfull _, ?_⟩
  intro t
  have hh := he t
  simp only [← hρval] at hh
  change h t = ∏ i, (if t i then h (DiagonalSlices.singleWord i) else 1)
  apply Subtype.val_injective
  refine hh.trans ?_
  symm
  change AlgebraicComplex.subtype (∏ i, (if t i then h (DiagonalSlices.singleWord i) else 1)) = _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  cases t i <;> rfl

/-- A large logical cube exposed by actual matching cards factors over its
proved original perfect pairing. The original scale is retained. -/
theorem logical_large_factorization (P1 : Paper1DiagonalSlicesAccepted)
    {n : ℕ} (f : Signature AlgebraicComplex n) (P : Pairing n)
    (hP : 4 ≤ P.count) (hF : support f ⊆ equalityCode P) (h0 : f (fun _ => false) ≠ 0)
    (s : AlgebraicComplex) (hs : s ≠ 0)
    (hcards : ∀ a b (hab : a ≠ b), plusContraction a b hab s f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab s f))
    (hprod : ∀ a b (hab : a ≠ b), Product
      (Tensor.reindex (Fintype.equivFin (EndpointSelfLoop.Remaining a b)) (plusContraction a b hab s f))) :
    ∃ ρ : Fin P.count → AlgebraicComplex, (∀ i, ρ i ≠ 0) ∧
      ∀ t, f (blockWord P t) = f (fun _ => false) * ∏ i, (if t i then ρ i else 1) := by
  have hfull := logical_full_support f P (by omega) hF h0 s hcards
  have hd := logical_unary_diagonals f P (by omega) hF h0 s hs hcards hprod
  let h : Signature AlgebraicComplex P.count := fun t => (f (fun _ => false))⁻¹ * f (blockWord P t)
  have hfull' : ∀ t, h t ≠ 0 := fun t => mul_ne_zero (inv_ne_zero h0) (hfull t)
  have hzero : h (fun _ => false) = 1 := by
    change (f (fun _ => false))⁻¹ * f (fun _ => false) = 1
    exact inv_mul_cancel₀ h0
  obtain ⟨ρ, hρ, he⟩ := diagonal_large_algebraic P1 hP h hfull' hzero
    (unaryDiagonals_scale _ hd _ (inv_ne_zero h0))
  refine ⟨ρ, hρ, ?_⟩
  intro t
  have ht := congrArg (fun z => f (fun _ => false) * z) (he t)
  simpa only [h, ← mul_assoc, mul_inv_cancel₀ h0, one_mul] using ht

end
end Paper2.HeightOne.Cyclic
