import Paper2.HeightOne.PhaseCards.FieldSaturation

/-! Fixed original-field control after a legal diagonal normalization. The
coordinate matrix may leave the field, but its inverse is applied to every
retained tensor before testing field membership. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable ExactInput GroupSplit

/-- This is the source ledger's projective pullback condition. -/
def PullbackOver (E : Subfield AlgebraicComplex) (A : InvertibleKernel)
    (f : AnySignature AlgebraicComplex) : Prop := ProjectivelyOver E (A.symm.action f.2)

lemma pullbackOver_global (E : Subfield AlgebraicComplex) (A D : InvertibleKernel)
    (f : AnySignature AlgebraicComplex) :
    PullbackOver E (D.comp A) ⟨f.1, D.action f.2⟩ ↔ PullbackOver E A f := by
  simp [PullbackOver]

/-- Inverse actual graph transport gives the field condition for every gadget,
with precisely the nonzero edge multiplier from the diagonal transport proof. -/
theorem network_pullbackOver (E : Subfield AlgebraicComplex) (A : InvertibleKernel)
    (a b : AlgebraicComplex) (hA : A.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    {F : SignatureFamily AlgebraicComplex} (hF : ∀ f ∈ F, PullbackOver E A f)
    {n : ℕ} {f : Signature AlgebraicComplex n} (hf : NetworkRealizable F f) :
    PullbackOver E A ⟨n, f⟩ := by
  have hi := inverse_diagonal A a b hA ha hb
  obtain ⟨c, hc, hreal⟩ := realizable_diagonal_transport hf A.symm a⁻¹ b⁻¹ hi
    (inv_ne_zero ha) (inv_ne_zero hb)
  have hf' : ∀ g ∈ familyAction A.symm F, ProjectivelyOver E g.2 := by
    rintro g ⟨f, hf, rfl⟩
    exact hF f hf
  have h := network_projectivelyOver E hf' hreal
  have hh := h.scale (inv_ne_zero hc)
  simpa only [PullbackOver, smul_smul, inv_mul_cancel₀ hc, one_smul] using hh

/-- Tensor action distributes through the actual ordered factorization. Thus
arbitrary selected factors satisfy the same original-field pullback condition. -/
lemma selectedFactors_pullbackOver (E : Subfield AlgebraicComplex) (A : InvertibleKernel)
    {f g : AnySignature AlgebraicComplex} (hf : PullbackOver E A f)
    (hg : g ∈ selectedFactors f) : PullbackOver E A g := by
  unfold selectedFactors at hg
  split_ifs at hg with hpos
  · obtain ⟨i, rfl⟩ := hg
    let Q := selectedDecomposition f hpos
    have hQ := selectedDecomposition_spec f hpos
    have hval : (Q.mapAction A.inverse).value = A.symm.action f.2 := by
      rw [TensorDecomposition.value_mapAction, hQ.1]
      rfl
    have hn : (Q.mapAction A.inverse).value ≠ 0 := by
      rw [hval]
      intro hz
      have h := congrArg A.action hz
      rw [A.action_symm_action] at h
      apply hpos.2
      simpa only [InvertibleKernel.action, Signature.coordinateAction_zero] using h
    exact Decomposition.factor_projectivelyOver (Q.mapAction A.inverse) E
      (hval.symm ▸ hf) hn i
  · exact False.elim hg

namespace BinaryMenu
variable {F : SignatureFamily AlgebraicComplex} (M : BinaryMenu F)

lemma produced_pullbackOver (E : Subfield AlgebraicComplex) (A : InvertibleKernel)
    (a b : AlgebraicComplex) (hA : A.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hF : ∀ f ∈ F, PullbackOver E A f)
    (f : AnySignature AlgebraicComplex) (hf : PullbackOver E A f) (k : M.Choices f) :
    PullbackOver E A (M.produced f k) := by
  apply network_pullbackOver E A a b hA ha hb (F := insert f F)
  · intro g hg
    rcases hg with rfl | hg
    · exact hf
    · exact hF g hg
  · exact M.produced_realizable (Set.subset_insert _ _) f (Set.mem_insert _ _) k

lemma next_pullbackOver (E : Subfield AlgebraicComplex) (A : InvertibleKernel)
    (a b : AlgebraicComplex) (hA : A.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hF : ∀ f ∈ F, PullbackOver E A f)
    {f g : AnySignature AlgebraicComplex} (hf : PullbackOver E A f)
    (hg : g ∈ M.next f) : PullbackOver E A g := by
  rcases hg with hg | ⟨k, rfl, _⟩
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
    exact selectedFactors_pullbackOver E A (M.produced_pullbackOver E A a b hA ha hb hF f hf k) hk
  · exact M.produced_pullbackOver E A a b hA ha hb hF f hf k

/-- The exact full saturation preserves the original frozen coefficient field
across the current legal diagonal normalization. No new field is chosen. -/
theorem finite_factor_closed_saturation_pullback
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (hfac : FactorClosed L.family)
    (E : Subfield AlgebraicComplex) (A : InvertibleKernel)
    (a b : AlgebraicComplex) (hA : A.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hfield : ∀ f ∈ L.family, PullbackOver E A f) :
    ∃ B : Language, RetainedExtension L B ∧ FactorClosed B.family ∧
      (∀ f ∈ B.family, M.Processed f B) ∧ (∀ f ∈ B.family, PullbackOver E A f) := by
  obtain ⟨B, hB, hfacB, hprocessed, hreach⟩ :=
    M.finite_factor_closed_saturation PG PR PF L hL htwo hFL hfac
  refine ⟨B, hB, hfacB, hprocessed, ?_⟩
  intro g hg
  obtain ⟨f, hf, hfg⟩ := hreach g hg
  have hF : ∀ f ∈ F, PullbackOver E A f := fun f hf => hfield f (hFL hf)
  clear hg
  induction hfg with
  | refl => exact hfield f hf
  | tail _ hb' ih => exact M.next_pullbackOver E A a b hA ha hb hF ih hb'

end BinaryMenu
end
end Paper2.HeightOne.PhaseCards
