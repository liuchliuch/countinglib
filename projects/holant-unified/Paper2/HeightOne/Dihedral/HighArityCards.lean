import Paper2.HeightOne.Dihedral.HighArityMonomial
import Holant.Dihedral.TwoCardLocalization.ThreeFactor

/-! Two nonzero contractions of a matching product have the same matching.
The contraction matrices may be arbitrary nonsingular monomial matrices;
their phase order and coefficient ratios are not enlarged or assumed. -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Holant Holant.Marked Holant.Certificates
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.TwoCardLocalization
open Holant.Dihedral.CompatibleClosure (pairOrder)
set_option backward.isDefEq.respectTransparency false

def CommonMatching {n : ℕ} (q₀ q₁ : Signature Scalar n) : Prop :=
  ∃ r : ℕ, ∃ p : (Fin r × Bool) ≃ Fin n, ∃ A₀ A₁ : Fin r → Mat, ∃ κ₀ κ₁ : Scalar,
    (∀ e,IsMonomial (A₀ e)) ∧ (∀ e,IsMonomial (A₁ e)) ∧ κ₀ ≠ 0 ∧ κ₁ ≠ 0 ∧
    q₀ = productValue p A₀ κ₀ ∧ q₁ = productValue p A₁ κ₁

theorem commonMatching_reindexed {n : ℕ} {E P : Type*}
    [Fintype E] [DecidableEq E] [DecidableEq P]
    (p : (E × Bool) ≃ P) (order : P ≃ Fin n) (A₀ A₁ : E → Mat) (κ₀ κ₁ : Scalar)
    (hA₀ : ∀ e,IsMonomial (A₀ e)) (hA₁ : ∀ e,IsMonomial (A₁ e))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) :
    CommonMatching (Tensor.reindex order (productValue p A₀ κ₀))
      (Tensor.reindex order (productValue p A₁ κ₁)) := by
  let e := Fintype.equivFin E
  let p' := (Equiv.prodCongr e.symm (Equiv.refl Bool)).trans (p.trans order)
  refine ⟨Fintype.card E,p',fun i => A₀ (e.symm i),fun i => A₁ (e.symm i),κ₀,κ₁,
    fun _ => hA₀ _,fun _ => hA₁ _,hκ₀,hκ₁,?_,?_⟩
  · exact (Presentation.ofFinite_tensor (p.trans order) A₀ κ₀).symm
  · exact (Presentation.ofFinite_tensor (p.trans order) A₁ κ₁).symm

theorem different_not_common {n : ℕ} {q₀ q₁ : Signature Scalar n}
    (h : DifferentProducts monomialGroup n q₀ q₁) : ¬ CommonMatching q₀ q₁ := by
  obtain ⟨M₀,M₁,hM₀,hM₁,hc₀,hc₁,hq₀,hq₁,hne⟩ := h
  rintro ⟨r,p,A₀,A₁,κ₀,κ₁,hA₀,hA₁,hκ₀,hκ₁,hQ₀,hQ₁⟩
  have he₀ := product_matching_unique p M₀.ports A₀ M₀.matrix κ₀ M₀.scalar hA₀
    (fun e => (safe_monomial_iff _).mp (hM₀ e)) hκ₀ hc₀ (hQ₀.symm.trans hq₀)
  have he₁ := product_matching_unique p M₁.ports A₁ M₁.matrix κ₁ M₁.scalar hA₁
    (fun e => (safe_monomial_iff _).mp (hM₁ e)) hκ₁ hc₁ (hQ₁.symm.trans hq₁)
  apply hne
  apply Equiv.ext
  intro u
  exact congrArg (fun M : Holant.Dihedral.EndpointParallelogram.Pairing (Fin n) => M.mate u)
    (he₀.symm.trans he₁)

private theorem pairOrder_zero_one {n : ℕ} : pairOrder (0 : Fin (n+2)) 1 = Equiv.refl _ := by
  simp [pairOrder]

theorem matching_cards_common {n : ℕ} (q : Signature Scalar (n+2))
    (hq : MatchingOrZero monomialGroup q) (C₀ C₁ : Mat)
    (hC₀ : IsMonomial C₀) (hC₁ : IsMonomial C₁)
    (hn₀ : Signature.contract C₀ q ≠ 0) (hn₁ : Signature.contract C₁ q ≠ 0) :
    CommonMatching (Signature.contract C₀ q) (Signature.contract C₁ q) := by
  rcases hq with rfl | ⟨M,hM,hκ,rfl⟩
  · exact False.elim (hn₀ (by funext x; simp [Signature.contract]))
  let p := M.ports
  let A := M.matrix
  let e := (p.symm 0).1
  let f := (p.symm 1).1
  by_cases hef : e = f
  · let σ := sameMask p 0
    let p' := (flipSlots σ).trans p
    let A' := orientedFactors A σ
    have hA' : ∀ d,IsMonomial (A' d) := by
      intro d
      exact (safe_monomial_iff _).mp (orientedFactors_safe monomial_reversal A σ hM d)
    have hp : productValue p' A' M.scalar = M.tensor := reorient_product p A M.scalar σ
    obtain ⟨hu,hv⟩ := same_selected_ports p (0 : Fin (n+2)) 1 Fin.zero_ne_one hef
    change p' (e,false) = 0 at hu
    change p' (e,true) = 1 at hv
    have huv : p' (e,false) ≠ p' (e,true) := by rw [hu,hv]; exact Fin.zero_ne_one
    let order := (remainingOrder (p' (e,false)) (p' (e,true)) huv).symm
    have hc (C : Mat) : Signature.contract C M.tensor = Tensor.reindex order
        (productValue (deletePorts p' e) (fun d => A' d.val) (MatchingContractionClosure.trace (A' e) C * M.scalar)) := by
      have hh := congrArg (Tensor.reindex order) (contract_matched p' A' M.scalar e C)
      rw [contractPair_order,hp] at hh
      simpa only [hu,hv,pairOrder_zero_one,Equiv.refl_symm,Tensor.reindex_refl] using hh
    have ht (C : Mat) (hn : Signature.contract C M.tensor ≠ 0) :
        MatchingContractionClosure.trace (A' e) C * M.scalar ≠ 0 := by
      intro hz
      apply hn
      rw [hc]
      funext x
      simp [Tensor.reindex,productValue,hz]
    have hgood := commonMatching_reindexed (deletePorts p' e) order
      (fun d => A' d.val) (fun d => A' d.val) _ _
      (fun d => hA' d.val) (fun d => hA' d.val) (ht C₀ hn₀) (ht C₁ hn₁)
    rw [← hc,← hc] at hgood
    exact hgood
  · let σ := crossMask p 0 1
    let p' := (flipSlots σ).trans p
    let A' := orientedFactors A σ
    have hA' : ∀ d,SafeBinary monomialGroup (A' d) := orientedFactors_safe monomial_reversal A σ hM
    have hp : productValue p' A' M.scalar = M.tensor := reorient_product p A M.scalar σ
    obtain ⟨hu,hv⟩ := cross_selected_ports p (0 : Fin (n+2)) 1 hef
    change p' (e,true) = 0 at hu
    change p' (f,false) = 1 at hv
    have huv : p' (e,true) ≠ p' (f,false) := by rw [hu,hv]; exact Fin.zero_ne_one
    let order := (remainingOrder (p' (e,true)) (p' (f,false)) huv).symm
    have hc (C : Mat) : Signature.contract C M.tensor = Tensor.reindex order
        (productValue (splicePorts p' e f) (spliceFactors C A' e f) M.scalar) := by
      have hh := congrArg (Tensor.reindex order) (contract_cross p' A' M.scalar e f hef C)
      rw [contractPair_order,hp] at hh
      simpa only [hu,hv,pairOrder_zero_one,Equiv.refl_symm,Tensor.reindex_refl] using hh
    have hm (C : Mat) (hC : IsMonomial C) : ∀ d,IsMonomial (spliceFactors C A' e f d) :=
      fun d => (safe_monomial_iff _).mp (spliceFactors_safe monomial_matrix_group monomial_X C A' e f
        ((safe_monomial_iff C).mpr hC) hA' d)
    have hgood := commonMatching_reindexed (splicePorts p' e f) order
      (spliceFactors C₀ A' e f) (spliceFactors C₁ A' e f) M.scalar M.scalar
      (hm C₀ hC₀) (hm C₁ hC₁) hκ hκ
    rw [← hc,← hc] at hgood
    exact hgood

end
end Paper2.HeightOne.Dihedral.HighArity
