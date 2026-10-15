import Holant.Dihedral.SectorRuling.SegreAlgebra
import Holant.Dihedral.SectorRuling.CommonSupport
import Holant.Dihedral.CompatibleCoefficientLine.MatchingAgreement
import Paper2.SourceFaithful.SourceStatements.MatchingCosetFourCycle

/-! The common-support branch of manuscript Lemma 5.15. The three original
ordered matching presentations are aligned from their actual support sets.
Their literal linear relation then forces one common varying binary factor.

The different-support branch derives the half-size intersection, cancellation,
and arbitrary-port four-cycle geometry from the original actual products.
No support coincidence, common pairing, or ruling is inferred from the public
main dichotomy. -/
namespace Paper2.SourceFaithful.SourceStatements
noncomputable section
open Holant Holant.Marked Holant.Certificates
open Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.SectorRuling
open Holant.Dihedral.EndpointParallelogram
open Holant.Dihedral.TwoCardLocalization
set_option backward.isDefEq.respectTransparency false

/-- Three nonzero monomial matching products with the same support and a
nontrivial linear relation lie in one ruling. Both edge alignments, including
their original endpoint reversals, are conclusions of the actual support
equalities. Every factor outside the one displayed edge is common up to a
nonzero scalar in all three original products. -/
theorem same_support_three_matching_products {r : ℕ}
    (p₀ p₁ p₂ : (Fin (r+1) × Bool) ≃ Fin (2*r+2))
    (A₀ A₁ A₂ : Fin (r+1) → Mat) (κ₀ κ₁ κ₂ a b : Scalar)
    (hA₀ : ∀ e, IsMonomial (A₀ e))
    (hA₁ : ∀ e, IsMonomial (A₁ e))
    (hA₂ : ∀ e, IsMonomial (A₂ e))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (hκ₂ : κ₂ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (h01 : support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)) =
      support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁)))
    (h02 : support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)) =
      support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂)))
    (hrel : Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂ =
      combination a b (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)
        (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁)) :
    ∃ (L₁ : MatchingAlignment p₀ p₁) (L₂ : MatchingAlignment p₀ p₂)
      (varying : Fin (r+1)), ∀ e, e ≠ varying →
        ProjectivelyEqual (L₁.factors A₁ e) (A₀ e) ∧
        ProjectivelyEqual (L₂.factors A₂ e) (A₀ e) := by
  classical
  have hm₁ := matching_of_support_eq p₀ p₁ A₀ A₁ κ₀ κ₁ hA₀ hA₁ hκ₀ hκ₁ h01
  have hm₂ := matching_of_support_eq p₀ p₂ A₀ A₂ κ₀ κ₂ hA₀ hA₂ hκ₀ hκ₂ h02
  let L₁ := MatchingAlignment.ofMate p₀ p₁
    (fun u => congrArg (fun P : Holant.Dihedral.EndpointParallelogram.Pairing _ => P.mate u) hm₁)
  let L₂ := MatchingAlignment.ofMate p₀ p₂
    (fun u => congrArg (fun P : Holant.Dihedral.EndpointParallelogram.Pairing _ => P.mate u) hm₂)
  have hB₁ : ∀ e, IsMonomial (L₁.factors A₁ e) := by
    intro e
    unfold MatchingAlignment.factors
    split
    · exact (hA₁ _).transpose
    · exact hA₁ _
  have hB₂ : ∀ e, IsMonomial (L₂.factors A₂ e) := by
    intro e
    unfold MatchingAlignment.factors
    split
    · exact (hA₂ _).transpose
    · exact hA₂ _
  have h01' : support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)) =
      support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ (L₁.factors A₁) κ₁)) := by
    rw [L₁.product_eq]
    exact h01
  obtain ⟨α,hα⟩ := shared_parities p₀ A₀ (L₁.factors A₁) κ₀ κ₁ hA₀ hB₁ hκ₀ h01'
  have hrel' : Holant.Dihedral.CompatibleClosure.productValue p₀ (L₂.factors A₂) κ₂ =
      combination a b (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)
        (Holant.Dihedral.CompatibleClosure.productValue p₀ (L₁.factors A₁) κ₁) := by
    rw [L₂.product_eq,L₁.product_eq]
    exact hrel
  obtain ⟨v,hv⟩ := three_products_one_factor p₀ A₀ (L₁.factors A₁) (L₂.factors A₂)
    κ₀ κ₁ κ₂ a b hκ₀ hκ₁ ha hb α (fun e => (hα e).1) (fun e => (hα e).2) hrel'
  let varying : Fin (r+1) := v.getD ⟨0,by omega⟩
  refine ⟨L₁,L₂,varying,?_⟩
  intro e he
  have hve : v ≠ some e := by
    intro h
    subst v
    exact he (by simp [varying])
  have h₁ := hv e hve
  exact ⟨h₁,fixed_factor_in_span p₀ A₀ (L₁.factors A₁) (L₂.factors A₂)
    κ₀ κ₁ κ₂ a b hB₂ hκ₂ hrel' e h₁⟩

/-- Actual matching products with distinct supports and a third nontrivial
product on their line have a half-size support intersection. The third support
is precisely their symmetric difference, and every coefficient in the
intersection cancels. All affine support and cardinality premises are derived
from the nonsingular monomial factors on the original ordered ports. -/
theorem different_support_three_matching_products {s n : ℕ}
    (p₀ p₁ p₂ : (Fin s × Bool) ≃ Fin n)
    (A₀ A₁ A₂ : Fin s → Mat) (κ₀ κ₁ κ₂ a b : Scalar)
    (hA₀ : ∀ e, IsMonomial (A₀ e))
    (hA₁ : ∀ e, IsMonomial (A₁ e))
    (hA₂ : ∀ e, IsMonomial (A₂ e))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (hκ₂ : κ₂ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)) ≠
      support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁)))
    (hrel : Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂ =
      combination a b (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)
        (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁)) :
    let S₀ := support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀))
    let S₁ := support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁))
    let S₂ := support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂))
    S₂ = (S₀ \ S₁) ∪ (S₁ \ S₀) ∧ 2*(S₀ ∩ S₁).card = 2^s ∧
      (S₀ ∩ S₁).Nonempty ∧
      ∀ x ∈ S₀ ∩ S₁, coefficients (Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂) x = 0 := by
  classical
  let f₀ := coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)
  let f₁ := coefficients (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁)
  let f₂ := coefficients (Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂)
  have h₀ : (support f₀).card = 2^s := product_support_card p₀ A₀ κ₀ hA₀ hκ₀
  have h₁ : (support f₁).card = 2^s := product_support_card p₁ A₁ κ₁ hA₁ hκ₁
  have h₂ : (support f₂).card = 2^s := product_support_card p₂ A₂ κ₂ hA₂ hκ₂
  have hAffine (p : (Fin s × Bool) ≃ Fin n) (A : Fin s → Mat) (κ : Scalar)
      (hA : ∀ e, IsMonomial (A e)) (hκ : κ ≠ 0) :
      AffineClosed (support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p A κ))) := by
    obtain ⟨offset,hoffset⟩ := product_cardMatching p A κ hA hκ
    apply affineClosed_of_coset _ (Pairing.ofPorts p).code offset
    intro x
    exact (mem_support _ _).trans (hoffset x)
  have hhalf := affine_intersection_half (support f₀) (support f₁)
    (hAffine p₀ A₀ κ₀ hA₀ hκ₀) (hAffine p₁ A₁ κ₁ hA₁ hκ₁)
    (h₀.trans h₁.symm) hne
  have hrel' : f₂ = combination a b f₀ f₁ := by
    funext x
    exact congrFun hrel ((bitsEquiv (Fin n)).symm x)
  have h₂' : (support (combination a b f₀ f₁)).card = 2^s := by
    rw [← hrel']
    exact h₂
  have h := third_support_cancellation a b ha hb f₀ f₁ (2^s) (by positivity)
    h₀ h₁ h₂' (hhalf.trans_eq h₀)
  rw [← hrel'] at h
  exact h

/-- When the first two actual monomial products have the same support, a
nonzero monomial third product on their line has that support as well. The
common-support alternative therefore needs no separately supplied support
equality for the third signature. -/
theorem third_support_eq_of_first_two_eq {s n : ℕ}
    (p₀ p₁ p₂ : (Fin s × Bool) ≃ Fin n)
    (A₀ A₁ A₂ : Fin s → Mat) (κ₀ κ₁ κ₂ a b : Scalar)
    (hA₀ : ∀ e, IsMonomial (A₀ e)) (hA₂ : ∀ e, IsMonomial (A₂ e))
    (hκ₀ : κ₀ ≠ 0) (hκ₂ : κ₂ ≠ 0)
    (h01 : support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)) =
      support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁)))
    (hrel : Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂ =
      combination a b (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)
        (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁)) :
    support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)) =
      support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂)) := by
  classical
  have hsub : support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂)) ⊆
      support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)) := by
    intro x hx
    by_contra hn
    have h₀ : coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀) x = 0 := by
      simpa only [mem_support,not_not] using hn
    have h₁ : coefficients (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁) x = 0 := by
      have hn₁ := hn
      rw [h01] at hn₁
      simpa only [mem_support,not_not] using hn₁
    have h := congrFun hrel ((bitsEquiv (Fin n)).symm x)
    have hx' := (mem_support _ _).mp hx
    apply hx'
    change coefficients (Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂) x =
      a * coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀) x +
        b * coefficients (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁) x at h
    simpa only [h₀,h₁,mul_zero,add_zero] using h
  have h₀ : (support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀))).card = 2^s :=
    product_support_card p₀ A₀ κ₀ hA₀ hκ₀
  have h₂ : (support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂))).card = 2^s :=
    product_support_card p₂ A₂ κ₂ hA₂ hκ₂
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- The three original matching presentations in the different-support branch
of manuscript Lemma 5.15 differ on exactly four original ports and realize the
three different pairings there. Every other literal matched edge is common.
All geometric premises are derived from the actual monomial product relation,
in arbitrary arity. -/
theorem different_support_three_products_four_cycle {s n : ℕ}
    (p₀ p₁ p₂ : (Fin s × Bool) ≃ Fin n)
    (A₀ A₁ A₂ : Fin s → Mat) (κ₀ κ₁ κ₂ a b : Scalar)
    (hA₀ : ∀ e, IsMonomial (A₀ e))
    (hA₁ : ∀ e, IsMonomial (A₁ e))
    (hA₂ : ∀ e, IsMonomial (A₂ e))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (hκ₂ : κ₂ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)) ≠
      support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁)))
    (hrel : Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂ =
      combination a b (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)
        (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁)) :
    Nonempty (ThreePairingsFourCycle (Pairing.ofPorts p₀) (Pairing.ofPorts p₁)
      (Pairing.ofPorts p₂)) := by
  classical
  let S₀ := support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀))
  let S₁ := support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁))
  let S₂ := support (coefficients (Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂))
  obtain ⟨hshape,hhalf,hcommon,_⟩ := different_support_three_matching_products
    p₀ p₁ p₂ A₀ A₁ A₂ κ₀ κ₁ κ₂ a b hA₀ hA₁ hA₂ hκ₀ hκ₁ hκ₂ ha hb hne hrel
  obtain ⟨o₀,ho₀⟩ := product_cardMatching p₀ A₀ κ₀ hA₀ hκ₀
  obtain ⟨o₁,ho₁⟩ := product_cardMatching p₁ A₁ κ₁ hA₁ hκ₁
  obtain ⟨o₂,ho₂⟩ := product_cardMatching p₂ A₂ κ₂ hA₂ hκ₂
  have h₀ : S₀.card = 2^s := product_support_card p₀ A₀ κ₀ hA₀ hκ₀
  have h₁ : S₁.card = 2^s := product_support_card p₁ A₁ κ₁ hA₁ hκ₁
  apply three_matching_cosets_four_cycle (Pairing.ofPorts p₀) (Pairing.ofPorts p₁)
    (Pairing.ofPorts p₂) S₀ S₁ S₂ o₀ o₁ o₂
  · intro x; exact (mem_support _ _).trans (ho₀ x)
  · intro x; exact (mem_support _ _).trans (ho₁ x)
  · intro x; exact (mem_support _ _).trans (ho₂ x)
  · exact hne
  · exact hcommon
  · exact hhalf.trans h₀.symm
  · exact h₀.trans h₁.symm
  · exact hshape

end
end Paper2.SourceFaithful.SourceStatements

