import Paper2.SourceFaithful.HighHeightCompleteNormalization
import Paper2.SourceFaithful.HighHeightReconstruction

/-! The actual normalized finite extension closes every height at least five
through the internally proved matching reconstruction and two-copy hardness
graph.  No high-height classification is accepted as a parameter. -/
namespace Paper2.SourceFaithful.HighHeight
open Tractable ExactInput Paper2.HighHeightNormalization

theorem NormalizedMountain.hard_ge_five
    (G : Paper1DirectGadgetAccepted) (R : Paper1RestrictionAccepted)
    (E : Paper1EOAccepted) {L : Language} {d : ℕ}
    (hd : 5 ≤ d) (W : NormalizedMountain L d) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  apply normalized_mountain_hard_original G R E L W.stage.language W.stage.backward
    (by omega) W.mountain W.central W.leftEndpoint W.rightEndpoint W.endpoint_ne_zero
    W.central_eo W.coefficient W.matching W.deck W.coefficient_ne_zero
  · intro x
    rw [W.decomposition]
    rfl
  · exact W.member

/-- The nonzero-central branch of the original height-five-and-above route.
The sole external obligation here is the stated classification of genuine
small boundary graphs; the finite port-normalization construction is proved. -/
theorem nonzero_central_hard_ge_five
    (G : Paper1DirectGadgetAccepted) (Fac : Paper1FactorClosureAccepted)
    (R : Paper1RestrictionAccepted) (E : Paper1EOAccepted)
    (L : Language) {d : ℕ} (hd : 5 ≤ d)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (heven : ∀ g ∈ L.family, Even g.1)
    (hdiv : ∀ g ∈ L.family, Tensor.HalfChargeDivisible g.2 d)
    (hsmall : ∀ S : RetainedStage L d, ∀ {n : ℕ}
      (f : Signature AlgebraicComplex n), 0 < n → n < 2*d →
      NetworkRealizable S.language.family f → f ≠ 0 → Paper2.RelativeEO.IsARSProduct f)
    (M : Signature AlgebraicComplex (2*d)) (hM : IsMountain M)
    (hFn : Signature.centralRestriction M ≠ 0)
    (hmem : (⟨2*d,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨W⟩ := finite_port_normalization G Fac R L (by omega) hpre htwo heven hdiv hsmall
    M (Signature.centralRestriction M) (M (fun _ => false)) (M (fun _ => true))
    (mul_ne_zero hM.zero_ne_zero hM.one_ne_zero) (centralRestriction_chargeLayer M) hFn
    (mountain_central_decomposition M hM) hmem
  exact W.hard_ge_five G R E hd

end Paper2.SourceFaithful.HighHeight
