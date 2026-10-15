import Paper2.HeightOne.Dihedral.HighArityPhaseChoice

/-! Two literal protected original factor lines on one common matching. The
indices name actual matrix entries in the complete coefficient products. -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
set_option backward.isDefEq.respectTransparency false

def TwoTags (n : ℕ) (q₀ q₁ : Signature Scalar n) : Prop :=
  ∃ r : ℕ, ∃ p : (Fin r × Bool) ≃ Fin n, ∃ A₀ A₁ : Fin r → Mat, ∃ κ₀ κ₁ : Scalar,
    (∀ e,IsMonomial (A₀ e)) ∧ (∀ e,IsMonomial (A₁ e)) ∧ κ₀ ≠ 0 ∧ κ₁ ≠ 0 ∧
    q₀=MatchingContractionClosure.productValue p A₀ κ₀ ∧
    q₁=MatchingContractionClosure.productValue p A₁ κ₁ ∧
    ∃ e f : Fin r,e ≠ f ∧ ¬ ProjectivelyEqual (A₁ e) (A₀ e) ∧ ¬ ProjectivelyEqual (A₁ f) (A₀ f)

/-- Finite edge re-enumeration keeps the exact two protected matrix entries. -/
theorem two_tags_of_finite {n : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
    (p : (E × Bool) ≃ Fin n) (A₀ A₁ : E → Mat) (κ₀ κ₁ : Scalar)
    (hA₀ : ∀ e,IsMonomial (A₀ e)) (hA₁ : ∀ e,IsMonomial (A₁ e))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (e f : E) (hef : e ≠ f)
    (he : ¬ ProjectivelyEqual (A₁ e) (A₀ e)) (hf : ¬ ProjectivelyEqual (A₁ f) (A₀ f)) :
    TwoTags n (MatchingContractionClosure.productValue p A₀ κ₀)
      (MatchingContractionClosure.productValue p A₁ κ₁) := by
  let s := Fintype.equivFin E
  let p' := (Equiv.prodCongr s.symm (Equiv.refl Bool)).trans p
  refine ⟨Fintype.card E,p',fun d => A₀ (s.symm d),fun d => A₁ (s.symm d),κ₀,κ₁,
    fun d => hA₀ _,fun d => hA₁ _,hκ₀,hκ₁,?_,?_,s e,s f,fun h => hef (s.injective h),?_,?_⟩
  · exact (MatchingContractionClosure.Presentation.ofFinite_tensor p A₀ κ₀).symm
  · exact (MatchingContractionClosure.Presentation.ofFinite_tensor p A₁ κ₁).symm
  · simpa only [Equiv.symm_apply_apply] using he
  · simpa only [Equiv.symm_apply_apply] using hf

/-- The concrete residual-port surgery can be put in any proved external order
without changing protected factor lines or the complete coefficients. -/
theorem two_tags_reindexed {n : ℕ} {E P : Type*} [Fintype E] [DecidableEq E]
    [DecidableEq P] (p : (E × Bool) ≃ P) (order : P ≃ Fin n)
    (A₀ A₁ : E → Mat) (κ₀ κ₁ : Scalar)
    (hA₀ : ∀ e,IsMonomial (A₀ e)) (hA₁ : ∀ e,IsMonomial (A₁ e))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (e f : E) (hef : e ≠ f)
    (he : ¬ ProjectivelyEqual (A₁ e) (A₀ e)) (hf : ¬ ProjectivelyEqual (A₁ f) (A₀ f)) :
    TwoTags n (Tensor.reindex order (MatchingContractionClosure.productValue p A₀ κ₀))
      (Tensor.reindex order (MatchingContractionClosure.productValue p A₁ κ₁)) :=
  two_tags_of_finite (p.trans order) A₀ A₁ κ₀ κ₁ hA₀ hA₁ hκ₀ hκ₁ e f hef he hf

theorem TwoTags.scale {n : ℕ} {q₀ q₁ : Signature Scalar n} (h : TwoTags n q₀ q₁)
    (c : Scalar) (hc : c ≠ 0) : TwoTags n (c • q₀) (c • q₁) := by
  obtain ⟨r,p,A₀,A₁,κ₀,κ₁,hA₀,hA₁,hκ₀,hκ₁,rfl,rfl,he⟩ := h
  refine ⟨r,p,A₀,A₁,c*κ₀,c*κ₁,hA₀,hA₁,mul_ne_zero hc hκ₀,mul_ne_zero hc hκ₁,?_,?_,he⟩
  all_goals funext x; simp [MatchingContractionClosure.productValue,Pi.smul_apply,smul_eq_mul,mul_assoc]

theorem TwoTags.nonzero {n : ℕ} {q₀ q₁ : Signature Scalar n}
    (h : TwoTags n q₀ q₁) : q₀ ≠ 0 ∧ q₁ ≠ 0 := by
  obtain ⟨r,p,A₀,A₁,κ₀,κ₁,hA₀,hA₁,hκ₀,hκ₁,rfl,rfl,_⟩ := h
  have hn₀ e := MatchingContractionClosure.SafeBinary.nonsingular monomial_matrix_group
    ((safe_monomial_iff (A₀ e)).mpr (hA₀ e))
  have hn₁ e := MatchingContractionClosure.SafeBinary.nonsingular monomial_matrix_group
    ((safe_monomial_iff (A₁ e)).mpr (hA₁ e))
  exact ⟨MatchingContractionClosure.productValue_nonzero p A₀ κ₀ hn₀ hκ₀,
    MatchingContractionClosure.productValue_nonzero p A₁ κ₁ hn₁ hκ₁⟩

end
end Paper2.HeightOne.Dihedral.HighArity
