import Paper2.HeightOne.Cyclic.QuaternaryPhases
import Paper2.HeightOne.PhaseCards.Paper1Pencil

/-! The full coefficient equivalence in source Lemma 5.12. The input is
only the six local ordered phase pencils of one four-port table. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.Cyclic HeightOne.PhaseCards

def CyclicNormalForm (N : ℕ) (p t : AlgebraicComplex)
    (x y : Fin 3 → AlgebraicComplex) : Prop :=
  (p ≠ 0 ∧ t ≠ 0 ∧ ∃ lambda, Root N lambda ∧ t = lambda * p ∧
    ∀ i, (x i = 0 ∧ y i = 0) ∨
      ∃ α, Root N α ∧ x i = -p * lambda / α ∧ y i = -p * α) ∨
  (p = 0 ∧ t = 0 ∧ ∀ i, (x i = 0 ∧ y i = 0) ∨
    ∃ ρ α, ρ ≠ 0 ∧ Root N α ∧ x i = ρ ∧ y i = ρ * α)

lemma zero_pair_relations {N : ℕ} {p t : AlgebraicComplex}
    (lambda : AlgebraicComplex) (hlambda : Root N lambda) (ht : t = lambda * p) :
    Relation N p 0 0 t ∧ Relation N p 0 0 t := by
  exact ⟨⟨lambda,hlambda,Or.inr (Or.inl ⟨rfl,rfl,ht⟩)⟩,
    ⟨lambda,hlambda,Or.inr (Or.inl ⟨rfl,rfl,ht⟩)⟩⟩

lemma live_pair_relations {N : ℕ} (hN : 0 < N) (p lambda α : AlgebraicComplex)
    (hlambda : Root N lambda) (hα : Root N α) :
    Relation N p (-p * lambda / α) (-p * α) (lambda * p) ∧
      Relation N p (-p * α) (-p * lambda / α) (lambda * p) := by
  have hα0 := root_ne_zero hN hα
  constructor
  · refine ⟨α,hα,Or.inl ⟨by ring,?_⟩⟩
    field_simp
  · refine ⟨lambda / α,root_div hlambda hα,Or.inl ⟨by ring,?_⟩⟩
    field_simp

lemma central_pair_relations {N : ℕ} (hN : 0 < N) (ρ α : AlgebraicComplex)
    (hα : Root N α) :
    Relation N 0 ρ (ρ * α) 0 ∧ Relation N 0 (ρ * α) ρ 0 := by
  have hα0 := root_ne_zero hN hα
  constructor
  · exact ⟨α,hα,Or.inr (Or.inr ⟨rfl,rfl,by ring⟩)⟩
  · refine ⟨1 / α,root_div (by simp [Root]) hα,Or.inr (Or.inr ⟨rfl,rfl,?_⟩)⟩
    field_simp

theorem cyclic_rows_iff_normalForm {N : ℕ} (hN : 0 < N)
    (p t : AlgebraicComplex) (x y : Fin 3 → AlgebraicComplex) :
    QuaternaryRows N p t x y ↔ CyclicNormalForm N p t x y := by
  constructor
  · intro h
    by_cases hp : p = 0
    · have ht := (paired_relation_endpoints hN (h 0).1 (h 0).2).mp hp
      right
      refine ⟨hp,ht,?_⟩
      subst p; subst t
      intro i
      obtain ⟨α,hα,hy⟩ := shared_cyclic_zero hN h i
      by_cases hx : x i = 0
      · exact Or.inl ⟨hx,by simp [hy,hx]⟩
      · exact Or.inr ⟨x i,α,hx,hα,rfl,by rw [hy]; ring⟩
    · obtain ⟨lambda,hlambda,ht,hpairs⟩ := shared_cyclic_live hN hp h
      left
      refine ⟨hp,by rw [ht]; exact mul_ne_zero (root_ne_zero hN hlambda) hp,
        lambda,hlambda,ht,?_⟩
      intro i
      obtain ⟨α,hα,hz | hl⟩ := hpairs i
      · exact Or.inl hz
      · exact Or.inr ⟨α,hα,hl⟩
  · rintro (⟨_,_,lambda,hlambda,ht,hp⟩ | ⟨rfl,rfl,hp⟩) i
    · rcases hp i with ⟨hx,hy⟩ | ⟨α,hα,hx,hy⟩
      · rw [hx,hy]; exact zero_pair_relations lambda hlambda ht
      · rw [hx,hy,ht]; exact live_pair_relations hN p lambda α hlambda hα
    · rcases hp i with ⟨hx,hy⟩ | ⟨ρ,α,_,hα,hx,hy⟩
      · rw [hx,hy]; exact zero_pair_relations 1 (by simp [Root]) (by simp)
      · rw [hx,hy]; exact central_pair_relations hN ρ α hα

def CyclicPencils (N : ℕ) (p t : AlgebraicComplex)
    (x y : Fin 3 → AlgebraicComplex) : Prop :=
  ∀ i, Safe N p (x i) (y i) t ∧ Safe N p (y i) (x i) t

theorem cyclic_pencils_iff_normalForm {N : ℕ} (hN : 3 ≤ N)
    (p t : AlgebraicComplex) (x y : Fin 3 → AlgebraicComplex) :
    CyclicPencils N p t x y ↔ CyclicNormalForm N p t x y := by
  rw [← cyclic_rows_iff_normalForm (by omega)]
  unfold CyclicPencils QuaternaryRows
  simp_rw [provedPhasePencil.phasePencil_7_1 N hN]

theorem no_single_live_endpoint {N : ℕ} (hN : 3 ≤ N)
    {p t : AlgebraicComplex} {x y : Fin 3 → AlgebraicComplex}
    (h : CyclicPencils N p t x y) : p = 0 ↔ t = 0 := by
  have hr := (provedPhasePencil.phasePencil_7_1 N hN p (x 0) (y 0) t).mpr (h 0).1
  have hs := (provedPhasePencil.phasePencil_7_1 N hN p (y 0) (x 0) t).mpr (h 0).2
  exact paired_relation_endpoints (by omega) hr hs

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity
