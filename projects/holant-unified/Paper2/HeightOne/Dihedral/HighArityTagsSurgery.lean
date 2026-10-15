import Paper2.HeightOne.Dihedral.HighArityTagsProducts
import Holant.Dihedral.TwoCardLocalization.TaggedSurgery

/-! Actual delete/splice product formulas preserve the two indexed protected
factor lines. The protected matrices are literal entries of the output tables. -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
open Holant.Dihedral.TwoCardLocalization (remainingOrder contractPair_order)
set_option backward.isDefEq.respectTransparency false

variable {n r : ℕ}

theorem trace_two_tags (p : (Fin r × Bool) ≃ Fin (n+2)) (A₀ A₁ : Fin r → Mat)
    (κ₀ κ₁ : Scalar) (hA₀ : ∀ d,IsMonomial (A₀ d)) (hA₁ : ∀ d,IsMonomial (A₁ d))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (e f g : Fin r) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (he : ¬ ProjectivelyEqual (A₁ e) (A₀ e)) (hf : ¬ ProjectivelyEqual (A₁ f) (A₀ f))
    (C : Mat) (ht₀ : trace (A₀ g) C ≠ 0) (ht₁ : trace (A₁ g) C ≠ 0) :
    TwoTags n
      (Signature.contract C (Tensor.reindex (pairOrder (p (g,false)) (p (g,true))).symm
        (MatchingContractionClosure.productValue p A₀ κ₀)))
      (Signature.contract C (Tensor.reindex (pairOrder (p (g,false)) (p (g,true))).symm
        (MatchingContractionClosure.productValue p A₁ κ₁))) := by
  have huv : p (g,false) ≠ p (g,true) := by intro h; have hh := congrArg Prod.snd (p.injective h); cases hh
  let order := (remainingOrder (p (g,false)) (p (g,true)) huv).symm
  have hgood := two_tags_reindexed (MatchingContractionClosure.deletePorts p g) order
    (fun d => A₀ d.val) (fun d => A₁ d.val) (trace (A₀ g) C*κ₀) (trace (A₁ g) C*κ₁)
    (fun d => hA₀ d.val) (fun d => hA₁ d.val) (mul_ne_zero ht₀ hκ₀) (mul_ne_zero ht₁ hκ₁)
    ⟨e,heg⟩ ⟨f,hfg⟩ (fun h => hef (congrArg Subtype.val h)) he hf
  have h₀ := congrArg (Tensor.reindex order) (MatchingContractionClosure.contract_matched p A₀ κ₀ g C)
  have h₁ := congrArg (Tensor.reindex order) (MatchingContractionClosure.contract_matched p A₁ κ₁ g C)
  change _ = Tensor.reindex order (MatchingContractionClosure.productValue
    (MatchingContractionClosure.deletePorts p g) (fun d => A₀ d.val) (trace (A₀ g) C*κ₀)) at h₀
  change _ = Tensor.reindex order (MatchingContractionClosure.productValue
    (MatchingContractionClosure.deletePorts p g) (fun d => A₁ d.val) (trace (A₁ g) C*κ₁)) at h₁
  rw [←h₀,←h₁] at hgood
  rw [contractPair_order,contractPair_order] at hgood
  exact hgood

theorem cross_two_tags (p : (Fin r × Bool) ≃ Fin (n+2)) (A₀ A₁ : Fin r → Mat)
    (κ₀ κ₁ : Scalar) (hA₀ : ∀ d,IsMonomial (A₀ d)) (hA₁ : ∀ d,IsMonomial (A₁ d))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (e f g : Fin r) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (hf : ¬ ProjectivelyEqual (A₁ f) (A₀ f)) (C : Mat) (hC : IsMonomial C)
    (he : ¬ ProjectivelyEqual (fuse C (A₁ e) (A₁ g)) (fuse C (A₀ e) (A₀ g))) :
    TwoTags n
      (Signature.contract C (Tensor.reindex (pairOrder (p (e,true)) (p (g,false))).symm
        (MatchingContractionClosure.productValue p A₀ κ₀)))
      (Signature.contract C (Tensor.reindex (pairOrder (p (e,true)) (p (g,false))).symm
        (MatchingContractionClosure.productValue p A₁ κ₁))) := by
  have huv : p (e,true) ≠ p (g,false) := by intro h; exact heg (congrArg Prod.fst (p.injective h))
  let order := (remainingOrder (p (e,true)) (p (g,false)) huv).symm
  have hsafe (A : Fin r → Mat) (hA : ∀ d,IsMonomial (A d)) :
      ∀ d,IsMonomial (MatchingContractionClosure.spliceFactors C A e g d) := by
    intro d
    unfold MatchingContractionClosure.spliceFactors
    split
    · exact (hA e).mul hC |>.mul (hA g)
    · exact hA d.val
  have he' : ¬ ProjectivelyEqual (MatchingContractionClosure.spliceFactors C A₁ e g ⟨e,heg⟩)
      (MatchingContractionClosure.spliceFactors C A₀ e g ⟨e,heg⟩) := by
    simpa only [MatchingContractionClosure.spliceFactors,ite_true,Holant.Dihedral.TwoCardLocalization.shared_fuse] using he
  have hf' : ¬ ProjectivelyEqual (MatchingContractionClosure.spliceFactors C A₁ e g ⟨f,hfg⟩)
      (MatchingContractionClosure.spliceFactors C A₀ e g ⟨f,hfg⟩) := by
    simpa only [MatchingContractionClosure.spliceFactors,Ne.symm hef,ite_false] using hf
  have hgood := two_tags_reindexed (MatchingContractionClosure.splicePorts p e g) order
    (MatchingContractionClosure.spliceFactors C A₀ e g) (MatchingContractionClosure.spliceFactors C A₁ e g)
    κ₀ κ₁ (hsafe A₀ hA₀) (hsafe A₁ hA₁) hκ₀ hκ₁
    ⟨e,heg⟩ ⟨f,hfg⟩ (fun h => hef (congrArg Subtype.val h)) he' hf'
  have h₀ := congrArg (Tensor.reindex order) (MatchingContractionClosure.contract_cross p A₀ κ₀ e g heg C)
  have h₁ := congrArg (Tensor.reindex order) (MatchingContractionClosure.contract_cross p A₁ κ₁ e g heg C)
  rw [←h₀,←h₁] at hgood
  rw [contractPair_order,contractPair_order] at hgood
  exact hgood

end
end Paper2.HeightOne.Dihedral.HighArity
