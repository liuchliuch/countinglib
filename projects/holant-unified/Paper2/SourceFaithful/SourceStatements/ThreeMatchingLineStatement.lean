import Paper2.SourceFaithful.SourceStatements.CommonEdgeFactors

/-! The complete source Lemma 5.15 for original arbitrary-arity nonsingular
monomial matching products. Both alternatives and every alignment/factor ratio
are derived from the actual three products and their nontrivial linear relation.
-/
namespace Paper2.SourceFaithful.SourceStatements
noncomputable section
open Holant Holant.Marked Holant.Certificates
open Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.SectorRuling
open Holant.Dihedral.EndpointParallelogram
open Holant.Dihedral.TwoCardLocalization
set_option backward.isDefEq.respectTransparency false

/-- Manuscript Lemma 5.15. The common-support branch is one Segre ruling with
the two original ordered edge alignments recovered. In the other branch the
three different pairings occur on four distinct original ports, every outside
edge is literally shared, and the three actual outside factors are common up
to nonzero scalar with their original orientation accounted for.

The theorem permits proportional endpoints as well; the source's pairwise
nonproportionality hypothesis is unnecessary for this stronger conclusion.
Every positive even arity is covered by `r+1` original binary factors. -/
theorem source_5_15 {r : ℕ}
    (p₀ p₁ p₂ : (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (A₀ A₁ A₂ : Fin (r+1) → Mat) (κ₀ κ₁ κ₂ a b : Scalar)
    (hA₀ : ∀ e, IsMonomial (A₀ e))
    (hA₁ : ∀ e, IsMonomial (A₁ e))
    (hA₂ : ∀ e, IsMonomial (A₂ e))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (hκ₂ : κ₂ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hrel : Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂ =
      combination a b (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)
        (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁)) :
    (support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)) =
        support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁)) ∧
      ∃ (L₁ : MatchingAlignment p₀ p₁) (L₂ : MatchingAlignment p₀ p₂)
        (varying : Fin (r+1)), ∀ e, e ≠ varying →
          ProjectivelyEqual (L₁.factors A₁ e) (A₀ e) ∧
          ProjectivelyEqual (L₂.factors A₂ e) (A₀ e)) ∨
    (∃ C : ThreePairingsFourCycle (Pairing.ofPorts p₀) (Pairing.ofPorts p₁)
        (Pairing.ofPorts p₂),
      ∀ e : Fin (r+1), p₀ (e,false) ≠ C.a → p₀ (e,false) ≠ C.b →
        p₀ (e,false) ≠ C.c → p₀ (e,false) ≠ C.d →
          ProjectivelyEqual (relativeFactor p₀ p₁ A₁ e) (A₀ e) ∧
          ProjectivelyEqual (relativeFactor p₀ p₂ A₂ e) (A₀ e)) := by
  classical
  by_cases h01 : support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)) =
      support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁))
  · have h02 := third_support_eq_of_first_two_eq p₀ p₁ p₂ A₀ A₁ A₂ κ₀ κ₁ κ₂ a b
      hA₀ hA₂ hκ₀ hκ₂ h01 hrel
    exact Or.inl ⟨h01,same_support_three_matching_products p₀ p₁ p₂ A₀ A₁ A₂
      κ₀ κ₁ κ₂ a b hA₀ hA₁ hA₂ hκ₀ hκ₁ hκ₂ ha hb h01 h02 hrel⟩
  · obtain ⟨C⟩ := different_support_three_products_four_cycle p₀ p₁ p₂ A₀ A₁ A₂
      κ₀ κ₁ κ₂ a b hA₀ hA₁ hA₂ hκ₀ hκ₁ hκ₂ ha hb h01 hrel
    refine Or.inr ⟨C,?_⟩
    intro e hea heb hec hed
    have hm₁ : (Pairing.ofPorts p₁).mate (p₀ (e,false)) = p₀ (e,true) := by
      simpa only [Pairing.ofPorts,Equiv.symm_apply_apply,Bool.not_false]
        using C.outside (p₀ (e,false)) hea heb hec hed
    have hm₂ : (Pairing.ofPorts p₂).mate (p₀ (e,false)) = p₀ (e,true) := by
      simpa only [Pairing.ofPorts,Equiv.symm_apply_apply,Bool.not_false]
        using C.third_outside (p₀ (e,false)) hea heb hec hed
    exact different_support_common_edge_factors p₀ p₁ p₂ A₀ A₁ A₂ κ₀ κ₁ κ₂ a b
      hA₀ hA₁ hA₂ hκ₀ hκ₁ hκ₂ ha hb h01 hrel e hm₁ hm₂

end
end Paper2.SourceFaithful.SourceStatements

