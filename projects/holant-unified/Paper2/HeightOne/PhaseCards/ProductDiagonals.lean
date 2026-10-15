import Paper2.HeightOne.PhaseCards.ProductPresentation
import Paper2.Paper1Accepted.DiagonalSlices

/-! A literal Product table that is nonzero on a diagonal has a unary-product
restriction there. All constraint factors become 1; no free variables are pinned. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.Tractable
noncomputable section
open scoped BigOperators

def ProductFactor.unaryWeight {n : ℕ} (p : ProductFactor n) (k : Fin n) (b : Bool) : AlgebraicComplex :=
  match p with
  | .unary j u _ => if k = j then u b else 1
  | .equality _ _ => 1
  | .disequality _ _ => 1

lemma ProductFactor.unaryWeight_ne_zero {n : ℕ} (p : ProductFactor n)
    (h : ∀ b, p.eval (fun _ => b) ≠ 0) (k : Fin n) (b : Bool) : p.unaryWeight k b ≠ 0 := by
  cases p with
  | unary j u hu =>
    by_cases hkj : k = j <;> simp only [unaryWeight, hkj, ↓reduceIte, ne_eq]
    · exact h b
    · exact one_ne_zero
  | equality i j => exact one_ne_zero
  | disequality i j => exact one_ne_zero

lemma ProductFactor.eval_eq_unaries {n : ℕ} (p : ProductFactor n) (t : Fin n → Bool)
    (ht : p.eval t ≠ 0) : p.eval t = ∏ k, p.unaryWeight k (t k) := by
  classical
  cases p with
  | unary j u hu => simp [ProductFactor.eval, ProductFactor.unaryWeight]
  | equality i j =>
    have he : Signature.equality (K := AlgebraicComplex) (t i) (t j) = 1 := by
      unfold Signature.equality at *
      split_ifs at * <;> simp_all [ProductFactor.eval, Signature.equality]
    simp [ProductFactor.eval, ProductFactor.unaryWeight, he]
  | disequality i j =>
    have he : Signature.disequality (K := AlgebraicComplex) (t i) (t j) = 1 := by
      unfold Signature.disequality at *
      split_ifs at * <;> simp_all [ProductFactor.eval, Signature.disequality]
    simp [ProductFactor.eval, ProductFactor.unaryWeight, he]

/-- The source's precise unary-product premise on each equal-coordinate
slice, proved from a concrete Product presentation and its live coefficients. -/
theorem Product.unaryOnDiagonal {n : ℕ} {f : Signature AlgebraicComplex n} (hf : Product f)
    (i j : Fin n) (hfull : ∀ t, t i = t j → f t ≠ 0) : DiagonalSlices.UnaryOnDiagonal f i j := by
  classical
  rcases hf with rfl | ⟨c, hc, ps, rfl⟩
  · exact False.elim (hfull (fun _ => false) rfl rfl)
  have hp (t : Fin n → Bool) (ht : t i = t j) (p : ProductFactor n) (hpm : p ∈ ps) : p.eval t ≠ 0 := by
    have hn := (mul_ne_zero_iff.mp (hfull t ht)).2
    intro hz
    exact hn (List.prod_eq_zero (List.mem_map.mpr ⟨p, hpm, hz⟩))
  refine ⟨c, fun k b => (ps.map (fun p => p.unaryWeight k b)).prod, hc, ?_, ?_⟩
  · intro k b
    apply List.prod_ne_zero
    intro hz
    obtain ⟨p, hpm, he⟩ := List.mem_map.mp hz
    exact p.unaryWeight_ne_zero (fun b => hp (fun _ => b) rfl p hpm) k b he
  · intro t ht
    dsimp only [productFormula]
    apply congrArg (fun x : AlgebraicComplex => c * x)
    have he : (ps.map (fun p => p.eval t)).prod =
        (ps.map (fun p => ∏ k, p.unaryWeight k (t k))).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro p hpm
      exact p.eval_eq_unaries t (hp t ht p hpm)
    rw [he]
    clear hfull hp he
    induction ps with
    | nil => simp
    | cons p ps ih =>
      simp only [List.map_cons, List.prod_cons, Finset.prod_mul_distrib, ih]

end
end Paper2.Tractable
