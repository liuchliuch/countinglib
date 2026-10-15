import Paper2.HeightOne.PhaseCards.ProjectiveField

/-! The precise saturation preserves a single original coefficient field up to
recorded nonzero tensor scales. This is a field statement about every actual
network and every selected factor, not a claim that arbitrary interpolation
can be used as a continuing state update. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable ExactInput
open scoped BigOperators

/-- Actual native-X graph evaluation preserves the projective coefficient field.
One normalization scalar is chosen for each vertex occurrence; their product
is retained and proved nonzero. -/
theorem network_projectivelyOver {K : Type} [Field K] (L : Subfield K)
    {F : SignatureFamily K} (hF : ∀ f ∈ F, ProjectivelyOver L f.2)
    {n : ℕ} {f : Signature K n} (hf : NetworkRealizable F f) : ProjectivelyOver L f := by
  classical
  obtain ⟨G, hU, hX, rfl⟩ := hf.ordered
  have hvertex : ∀ v : Fin G.shape.vertices,
      ∃ c : K, c ≠ 0 ∧ ∀ x, c * G.vertex v x ∈ L :=
    fun v => hF ⟨G.shape.arity v, G.vertex v⟩ (hU v)
  choose c hc hcoeff using hvertex
  refine ⟨∏ v, c v, Finset.prod_ne_zero_iff.mpr (fun v _ => hc v), ?_⟩
  intro x
  rw [Network.denote_nativeX G hX, Finset.mul_sum]
  apply L.sum_mem
  intro z _
  rw [← Finset.prod_mul_distrib]
  exact L.prod_mem (fun v _ => hcoeff v _)

lemma selectedFactors_projectivelyOver (L : Subfield AlgebraicComplex)
    {f g : AnySignature AlgebraicComplex} (hf : ProjectivelyOver L f.2)
    (hg : g ∈ selectedFactors f) : ProjectivelyOver L g.2 := by
  unfold selectedFactors at hg
  split_ifs at hg with hpos
  · obtain ⟨i, rfl⟩ := hg
    have hQ := selectedDecomposition_spec f hpos
    apply Decomposition.factor_projectivelyOver (selectedDecomposition f hpos) L
    · rwa [hQ.1]
    · rw [hQ.1]
      exact hpos.2
  · exact False.elim hg

namespace BinaryMenu
variable {F : SignatureFamily AlgebraicComplex} (M : BinaryMenu F)

lemma produced_projectivelyOver (L : Subfield AlgebraicComplex)
    (hF : ∀ f ∈ F, ProjectivelyOver L f.2)
    (f : AnySignature AlgebraicComplex) (hf : ProjectivelyOver L f.2) (k : M.Choices f) :
    ProjectivelyOver L (M.produced f k).2 := by
  apply network_projectivelyOver L (F := insert f F)
  · intro g hg
    rcases hg with rfl | hg
    · exact hf
    · exact hF g hg
  · exact M.produced_realizable (Set.subset_insert _ _) f (Set.mem_insert _ _) k

lemma next_projectivelyOver (L : Subfield AlgebraicComplex)
    (hF : ∀ f ∈ F, ProjectivelyOver L f.2)
    {f g : AnySignature AlgebraicComplex} (hf : ProjectivelyOver L f.2)
    (hg : g ∈ M.next f) : ProjectivelyOver L g.2 := by
  rcases hg with hg | ⟨k, rfl, _⟩
  · obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
    exact selectedFactors_projectivelyOver L (M.produced_projectivelyOver L hF f hf k) hk
  · exact M.produced_projectivelyOver L hF f hf k

lemma reach_projectivelyOver (L : Subfield AlgebraicComplex)
    (hF : ∀ f ∈ F, ProjectivelyOver L f.2)
    {f g : AnySignature AlgebraicComplex} (hf : ProjectivelyOver L f.2)
    (hg : Relation.ReflTransGen (fun a b => b ∈ M.next a) f g) :
    ProjectivelyOver L g.2 := by
  induction hg with
  | refl => exact hf
  | tail _ hb ih => exact M.next_projectivelyOver L hF ih hb

/-- In fixed coordinates the entire finite factor-closed saturation uses one
coefficient field. Prime factor choices cannot enlarge it projectively. -/
theorem finite_factor_closed_saturation_over_field
    (PG : Paper1DirectGadgetAccepted) (PR : Paper1RestrictionAccepted)
    (PF : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hFL : F ⊆ L.family) (hfac : FactorClosed L.family)
    (E : Subfield AlgebraicComplex) (hfield : ∀ f ∈ L.family, ProjectivelyOver E f.2) :
    ∃ B : Language, RetainedExtension L B ∧ FactorClosed B.family ∧
      (∀ f ∈ B.family, M.Processed f B) ∧
      (∀ f ∈ B.family, ProjectivelyOver E f.2) := by
  obtain ⟨B, hB, hfacB, hprocessed, hreach⟩ :=
    M.finite_factor_closed_saturation PG PR PF L hL htwo hFL hfac
  refine ⟨B, hB, hfacB, hprocessed, ?_⟩
  intro g hg
  obtain ⟨f, hf, hfg⟩ := hreach g hg
  exact M.reach_projectivelyOver E (fun f hf => hfield f (hFL hf)) (hfield f hf) hfg

end BinaryMenu
end
end Paper2.HeightOne.PhaseCards
