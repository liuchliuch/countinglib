import Holant.Proofs.FiniteGroups.UniqueType
import Holant.Projective.FiniteGroupFacts.Source

/-! Literal finite-group statements 2.1 and 2.2. The classification below
is actual conjugacy in the complex projective group, with a unique type and
integer parameter. It retains the cyclic and dihedral parameter restrictions
and the orders of all five standard models. The group facts are the proved
compound Paper 1 statement, whose eight clauses contain every listed fact
of Paper 2 Lemma 2.2. No graph realization or legal GO(X) normalization is
inferred from these group-theoretic conjugacies.
-/
namespace Paper2.SourceFaithful.SourceStatements.FiniteGroups
open Holant.Projective.BoundedTorsion
open Holant.Projective.FiniteGroupFacts
open Holant.Projective.FiniteSubgroupClassification
open Holant.LocalDrafts.FinitePGL2
noncomputable section

def modelOrder : ModelType → ℕ
  | .cyclic m => m
  | .dihedral m => 2 * m
  | .platonic p => Holant.Certificates.RainbowOrbit.size p

/-- The actual conjugate model has exactly the source's displayed order.
The three Platonic values of `size` are 12, 24 and 60. -/
theorem model_order (H : Subgroup (PGL2 ℂ)) (t : ModelType)
    (h : HasModel H t) : Nat.card H = modelOrder t := by
  cases t with
  | cyclic m =>
    obtain ⟨_,ω,hω,hc⟩ := h
    change Nat.card H = m
    exact hc.card_eq.trans (by rw [cyclicModel_card,← hω.eq_orderOf])
  | dihedral m =>
    obtain ⟨_,ω,hω,hc⟩ := h
    exact hc.card_eq.trans (dihedralModel_card hω)
  | platonic p =>
    exact h.card_eq.trans (modelPGL_card p)

/-- Source Proposition 2.1, including uniqueness of the actual conjugacy
type and its integer parameter, and the exact order of that type. -/
theorem proposition_2_1 (H : Subgroup (PGL2 ℂ)) [Finite H] :
    ∃! t : ModelType, HasModel H t ∧ Nat.card H = modelOrder t := by
  obtain ⟨t,ht,hu⟩ := finite_subgroup_exists_unique_model H
  exact ⟨t,⟨ht,model_order H t ht⟩,fun s hs => hu s hs.1⟩

/-- Source Lemma 2.2 in one compound checked interface. The finite cyclic
group is instantiated by C_m; its dihedral, A4, S4, A5 and genuine projective
centralizer clauses are all internally proved, with no structural premise.
-/
theorem lemma_2_2 (m : ℕ) (hm : 2 ≤ m) :
    Lemma22 (Multiplicative (ZMod m)) m := by
  haveI : NeZero m := ⟨by omega⟩
  exact finite_projective_group_facts (Multiplicative (ZMod m)) m hm

end
end Paper2.SourceFaithful.SourceStatements.FiniteGroups

