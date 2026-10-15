import Paper2.HeightOne.Dihedral.HighArityTagsTerminal
import Paper2.HeightOne.Dihedral.HighArityRigidity

/-! Two actual nonzero cards of a three-factor current-group product have one
fixed residual factor. Both cases use the literal original product extraction. -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure Holant.Certificates
open Holant.Dihedral.TwoCardLocalization (remainingOrder contractPair_order)
set_option backward.isDefEq.respectTransparency false

def ThreeFactor (q : Signature Scalar 6) : Prop :=
  ∃ p : (Fin 3 × Bool) ≃ Fin 6, ∃ A : Fin 3 → Mat, ∃ κ : Scalar,
    (∀ e,IsMonomial (A e)) ∧ κ ≠ 0 ∧ q=MatchingContractionClosure.productValue p A κ

private theorem pairOrder_zero_one {n : ℕ} : pairOrder (0 : Fin (n+2)) 1=Equiv.refl _ := by
  simp [pairOrder]

private theorem oriented_group {r : ℕ} (A : Fin r → Mat) (σ : Fin r → Bool)
    (hA : ∀ e,IsMonomial (A e)) : ∀ e,IsMonomial (MatchingContractionClosure.orientedFactors A σ e) := by
  intro e
  unfold MatchingContractionClosure.orientedFactors
  split
  · exact (hA e).transpose
  · exact hA e

private theorem splice_group {r : ℕ} (A : Fin r → Mat) (C : Mat) (e f : Fin r)
    (hA : ∀ d,IsMonomial (A d)) (hC : IsMonomial C) :
    ∀ d,IsMonomial (MatchingContractionClosure.spliceFactors C A e f d) := by
  intro d
  unfold MatchingContractionClosure.spliceFactors
  split
  · exact (hA e).mul hC |>.mul (hA f)
  · exact hA d.val

private theorem other_three (e : Fin 3) : ∃ g : Fin 3,g ≠ e := by fin_cases e <;> decide
private theorem third_three (e f : Fin 3) (hef : e ≠ f) : ∃ g : Fin 3,g ≠ e ∧ g ≠ f := by
  fin_cases e <;> fin_cases f <;> first | exact False.elim (hef rfl) | decide

/-- Deleting the selected pair either traces one original factor or fuses two;
the third original factor appears unchanged in BOTH actual residual tables. -/
theorem three_factor_cards_ruling  (q : Signature Scalar 6)
    (hq : ThreeFactor q) (C₀ C₁ : Mat) (hC₀ : IsMonomial C₀) (hC₁ : IsMonomial C₁)
    (hn₀ : Signature.contract C₀ q ≠ 0) (hn₁ : Signature.contract C₁ q ≠ 0) :
    RulingPair (Signature.contract C₀ q) (Signature.contract C₁ q) := by
  obtain ⟨p,A,κ,hA,hκ,rfl⟩ := hq
  let e := (p.symm 0).1
  let f := (p.symm 1).1
  by_cases hef : e=f
  · let σ := MatchingContractionClosure.sameMask p 0
    let p' := (MatchingContractionClosure.flipSlots σ).trans p
    let A' := MatchingContractionClosure.orientedFactors A σ
    have hA' : ∀ d,IsMonomial (A' d) := oriented_group A σ hA
    have hp : MatchingContractionClosure.productValue p' A' κ=MatchingContractionClosure.productValue p A κ :=
      MatchingContractionClosure.reorient_product p A κ σ
    obtain ⟨hu,hv⟩ := MatchingContractionClosure.same_selected_ports p (0 : Fin 6) 1 Fin.zero_ne_one hef
    change p' (e,false)=0 at hu
    change p' (e,true)=1 at hv
    have huv : p' (e,false) ≠ p' (e,true) := by rw [hu,hv]; exact Fin.zero_ne_one
    let order := (remainingOrder (p' (e,false)) (p' (e,true)) huv).symm
    have hc (C : Mat) : Signature.contract C (MatchingContractionClosure.productValue p A κ)=
        Tensor.reindex order (MatchingContractionClosure.productValue
          (MatchingContractionClosure.deletePorts p' e) (fun d => A' d.val)
          (MatchingContractionClosure.trace (A' e) C*κ)) := by
      have hh := congrArg (Tensor.reindex order) (MatchingContractionClosure.contract_matched p' A' κ e C)
      rw [contractPair_order,hp] at hh
      simpa only [hu,hv,pairOrder_zero_one,Equiv.refl_symm,Tensor.reindex_refl] using hh
    have ht₀ : MatchingContractionClosure.trace (A' e) C₀ ≠ 0 := by
      intro ht
      apply hn₀
      rw [hc]
      funext x
      simp [Tensor.reindex,MatchingContractionClosure.productValue,ht]
    have ht₁ : MatchingContractionClosure.trace (A' e) C₁ ≠ 0 := by
      intro ht
      apply hn₁
      rw [hc]
      funext x
      simp [Tensor.reindex,MatchingContractionClosure.productValue,ht]
    obtain ⟨g,hg⟩ : ∃ g : Fin 3,g ≠ e := other_three e
    have hgood := rulingPair_reindexed (MatchingContractionClosure.deletePorts p' e) order
      (fun d => A' d.val) (fun d => A' d.val)
      (MatchingContractionClosure.trace (A' e) C₀*κ) (MatchingContractionClosure.trace (A' e) C₁*κ)
      (fun d => hA' d.val) (fun d => hA' d.val) (mul_ne_zero ht₀ hκ) (mul_ne_zero ht₁ hκ)
      ⟨g,hg⟩ (ProjectivelyEqual.refl _)
    rw [←hc,←hc] at hgood
    exact hgood
  · let σ := MatchingContractionClosure.crossMask p 0 1
    let p' := (MatchingContractionClosure.flipSlots σ).trans p
    let A' := MatchingContractionClosure.orientedFactors A σ
    have hA' : ∀ d,IsMonomial (A' d) := oriented_group A σ hA
    have hp : MatchingContractionClosure.productValue p' A' κ=MatchingContractionClosure.productValue p A κ :=
      MatchingContractionClosure.reorient_product p A κ σ
    obtain ⟨hu,hv⟩ := MatchingContractionClosure.cross_selected_ports p (0 : Fin 6) 1 hef
    change p' (e,true)=0 at hu
    change p' (f,false)=1 at hv
    have huv : p' (e,true) ≠ p' (f,false) := by rw [hu,hv]; exact Fin.zero_ne_one
    let order := (remainingOrder (p' (e,true)) (p' (f,false)) huv).symm
    have hc (C : Mat) : Signature.contract C (MatchingContractionClosure.productValue p A κ)=
        Tensor.reindex order (MatchingContractionClosure.productValue
          (MatchingContractionClosure.splicePorts p' e f) (MatchingContractionClosure.spliceFactors C A' e f) κ) := by
      have hh := congrArg (Tensor.reindex order) (MatchingContractionClosure.contract_cross p' A' κ e f hef C)
      rw [contractPair_order,hp] at hh
      simpa only [hu,hv,pairOrder_zero_one,Equiv.refl_symm,Tensor.reindex_refl] using hh
    obtain ⟨g,hge,hgf⟩ : ∃ g : Fin 3,g ≠ e ∧ g ≠ f := third_three e f hef
    have hcommon : ProjectivelyEqual (MatchingContractionClosure.spliceFactors C₁ A' e f ⟨g,hgf⟩)
        (MatchingContractionClosure.spliceFactors C₀ A' e f ⟨g,hgf⟩) := by
      simp only [MatchingContractionClosure.spliceFactors,hge,ite_false]
      exact ProjectivelyEqual.refl _
    have hgood := rulingPair_reindexed (MatchingContractionClosure.splicePorts p' e f) order
      (MatchingContractionClosure.spliceFactors C₀ A' e f) (MatchingContractionClosure.spliceFactors C₁ A' e f)
      κ κ (splice_group A' C₀ e f hA' hC₀) (splice_group A' C₁ e f hA' hC₁) hκ hκ ⟨g,hgf⟩ hcommon
    rw [←hc,←hc] at hgood
    exact hgood

theorem matching_six_threeFactor (q : Signature Scalar 6)
    (hq : MatchingContractionClosure.MatchingOrZero monomialGroup q) (hn : q ≠ 0) :
    ThreeFactor q := by
  rcases hq with hq | ⟨M,hM,hκ,hq⟩
  · exact False.elim (hn hq)
  have hcount : M.edges = 3 := by
    have hh := Fintype.card_congr M.ports
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hh
    omega
  cases M with
  | mk edges ports matrix scalar =>
    dsimp only at hcount
    subst edges
    exact ⟨ports,matrix,scalar,fun e => (safe_monomial_iff _).mp (hM e),hκ,hq⟩

theorem phaseKernel_monomial {N : ℕ} (hN : 0 < N) (i : PhaseLabel N) :
    IsMonomial (phaseKernel i) :=
  M_isMonomial i.1 (neg_ne_zero.mpr (i.2.property.ne_zero hN))

/-- Actual negative-phase localization excludes two independent factor-line
discrepancies. The inherited six-port ancestor is proved to be a full matching
product from the first actual available kernel in the same program. -/
theorem no_two_tags_matching_cards {N : ℕ} (hN : 3 ≤ N)
    (r : ℕ) (hr : 1 ≤ r) (q : Signature Scalar (2*r+6))
    (hcards : ∀ i : PhaseLabel N,∀ p : Equiv.Perm (Fin (2*r+6)),
      MatchingContractionClosure.MatchingOrZero monomialGroup
        (Signature.contract (phaseKernel i) (Tensor.reindex p.symm q)))
    (C₀ C₁ : Mat) (hC₀ : IsMonomial C₀) (hC₁ : IsMonomial C₁) :
    ¬ TwoTags (2*r+4) (Signature.contract C₀ q) (Signature.contract C₁ q) := by
  intro h
  obtain ⟨P,hP,hout⟩ := two_tags_program hN r _ _ h
  have hanc := Program.core_matching_family_of_first_cards phaseKernel
    (phaseKernel_monomial (by omega)) P (by rw [hP]; omega) q hcards
  rw [← P.inherited_card,← P.inherited_card] at hout
  obtain ⟨hn₀,hn₁⟩ := hout.nonzero
  have hn : P.core phaseKernel q ≠ 0 := by
    intro hz
    apply hn₀
    rw [hz]
    funext x
    simp [Signature.contract]
  exact two_tags_not_ruling hout (three_factor_cards_ruling _
    (matching_six_threeFactor _ hanc hn) C₀ C₁ hC₀ hC₁ hn₀ hn₁)


end
end Paper2.HeightOne.Dihedral.HighArity
