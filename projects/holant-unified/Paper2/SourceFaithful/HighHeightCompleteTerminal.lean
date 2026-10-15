import Paper2.SourceFaithful.HighHeightCompleteReconstruction
import Paper2.SourceFaithful.RelativeEO.Terminal
import Paper2.SourceFaithful.HeightFour.Retained
import Paper2.SourceFaithful.GeneralizedEqualityTerminal

/-! The small-boundary obligation in finite port normalization follows from
the proved relative EO terminal for actual graphs.  This closes the nonzero
central branch at every height at least four without a normalization or
reconstruction oracle. -/
namespace Paper2.SourceFaithful.HighHeight
open Tractable ExactInput Paper2.RelativeEO Paper2.HighHeightNormalization

/-- Every positive nonzero small boundary of a retained stage is an actual EO
output, hence belongs to the algebraic ARS product class in the nonhard branch.
The charge argument uses all labels of the stage and the terminal transports
through the same concrete finite-stage reduction. -/
theorem retained_small_boundary_isARSProduct
    (G : Paper1DirectGadgetAccepted) (O : Paper1OccurrenceAccepted)
    (Fac : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted)
    {L : Language} {d : ℕ} (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L))
    (hnohard : ¬ FixedFieldOutput.SharpPHard .nativeX L)
    (S : RetainedStage L d) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : 0 < n) (hlt : n < 2*d)
    (hgraph : NetworkRealizable S.language.family f) (hf : f ≠ 0) :
    IsARSProduct f := by
  have hbothS : BothChargeSigns S.language.family := by
    obtain ⟨⟨g,hg,x,hx,hneg⟩,⟨h,hh,y,hy,hpos⟩⟩ := hboth
    exact ⟨⟨g,S.contains hg,x,hx,hneg⟩,⟨h,S.contains hh,y,hy,hpos⟩⟩
  have hnohardS : ¬ FixedFieldOutput.SharpPHard .nativeX S.language :=
    fun h => hnohard (h.transport S.backward)
  have heo : Tensor.ChargeLayer f 0 :=
    (realizable_small_boundary_eo f hlt
      (fun g hg => ⟨S.even g hg,S.divisible g hg⟩) hgraph).2
  exact RelativeEO.realized_isARSProduct G O Fac U E R B S.language S.preprocessed
    hbothS (S.nontractable hnot) hnohardS f hn hf
    ((centralSupport_iff_chargeLayer f).mpr heo)
    (NativeNetworkRealizesUpTo.of_realizable hgraph)

/-- A mountain with a nonzero central part closes every height at least four.
Height four uses the proved finite atlas and actual Bell endpoint; all larger
heights use the internally proved matching reconstruction and two-copy graph.
The no-hardness case needed during normalization is discharged locally. -/
theorem nonzero_central_hard_ge_four
    (P : Paper1Accepted) (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (Fac : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted) (N : Paper1NormalizationAccepted)
    (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L))
    (heven : ∀ g ∈ L.family, Even g.1)
    (hdiv : ∀ g ∈ L.family, Tensor.HalfChargeDivisible g.2 d)
    (M : Signature AlgebraicComplex (2*d)) (hM : IsMountain M)
    (hFn : Signature.centralRestriction M ≠ 0)
    (hmem : (⟨2*d,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases hh : FixedFieldOutput.SharpPHard .nativeX L
  · exact hh
  have hsmall : ∀ S : RetainedStage L d, ∀ {n : ℕ}
      (f : Signature AlgebraicComplex n), 0 < n → n < 2*d →
      NetworkRealizable S.language.family f → f ≠ 0 → IsARSProduct f :=
    retained_small_boundary_isARSProduct G O Fac U E R B hboth hnot hh
  have htwo := bothChargeSigns_not_oneSided hboth
  by_cases hd4 : d = 4
  · subst d
    obtain ⟨W⟩ := finite_port_normalization G Fac R L hd hpre htwo heven hdiv hsmall
      M (Signature.centralRestriction M) (M (fun _ => false)) (M (fun _ => true))
      (mul_ne_zero hM.zero_ne_zero hM.one_ne_zero) (centralRestriction_chargeLayer M) hFn
      (mountain_central_decomposition M hM) hmem
    exact HeightFour.retained_normalized_mountain_hard P G O Fac U E R N L hboth hnot W
  · exact nonzero_central_hard_ge_five G Fac R E L (by omega) hpre htwo heven hdiv
      hsmall M hM hFn hmem

/-- The whole-language alternative for a nonzero-central mountain.  Its two
endpoints supply both charge signs, so no ambient sign premise is needed. -/
theorem nonzero_central_classification_ge_four
    (P : Paper1Accepted) (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (Fac : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted) (N : Paper1NormalizationAccepted)
    (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (hpre : Preprocessed L.family)
    (heven : ∀ g ∈ L.family, Even g.1)
    (hdiv : ∀ g ∈ L.family, Tensor.HalfChargeDivisible g.2 d)
    (M : Signature AlgebraicComplex (2*d)) (hM : IsMountain M)
    (hFn : Signature.centralRestriction M ≠ 0)
    (hmem : (⟨2*d,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases ht : Tract (kImage L)
  · exact Or.inl ht
  · have hboth : BothChargeSigns L.family :=
      (commonOneSided_or_bothChargeSigns L.family).resolve_left
        (Paper2.HeightThree.mountain_not_commonOneSided L.family M hM hmem)
    exact Or.inr (nonzero_central_hard_ge_four P G O Fac U E R B N L hd hpre hboth ht
      heven hdiv M hM hFn hmem)

/-- Complete height-four-and-above mountain classification.  A vanishing
central part is a literal generalized equality; its actual two-copy native-X
graph supplies the quaternary EO terminal.  The other branch uses the finite
normalization, height-four atlas and arbitrary-height reconstruction proved
above.  No Paper 2 classification is supplied as an input. -/
theorem classification_ge_four
    (P : Paper1Accepted) (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (Fac : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted) (N : Paper1NormalizationAccepted)
    (L : Language) {d : ℕ} (hd : 4 ≤ d)
    (hpre : Preprocessed L.family)
    (heven : ∀ g ∈ L.family, Even g.1)
    (hdiv : ∀ g ∈ L.family, Tensor.HalfChargeDivisible g.2 d)
    (M : Signature AlgebraicComplex (2*d)) (hM : IsMountain M)
    (hmem : (⟨2*d,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases ht : Tract (kImage L)
  · exact Or.inl ht
  · have hboth : BothChargeSigns L.family :=
      (commonOneSided_or_bothChargeSigns L.family).resolve_left
        (Paper2.HeightThree.mountain_not_commonOneSided L.family M hM hmem)
    by_cases hcentral : Signature.centralRestriction M = 0
    · right
      apply generalized_equality_relative_terminal G O Fac U E R B L hpre hboth ht
        (by omega) M (M (fun _ => false)) (M (fun _ => true))
        (mul_ne_zero hM.zero_ne_zero hM.one_ne_zero)
      · intro x
        have hx := congrFun (mountain_central_decomposition M hM) x
        change M x = (if x = (fun _ => false) then M (fun _ => false) else 0) +
          (if x = (fun _ => true) then M (fun _ => true) else 0) +
          Signature.centralRestriction M x at hx
        rw [hcentral] at hx
        simpa only [Pi.zero_apply,add_zero] using hx
      · exact supplied_realizable hmem
    · exact Or.inr (nonzero_central_hard_ge_four P G O Fac U E R B N L hd hpre hboth ht
        heven hdiv M hM hcentral hmem)

end Paper2.SourceFaithful.HighHeight
