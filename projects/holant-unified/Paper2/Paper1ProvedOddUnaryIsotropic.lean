import Paper2.Paper1ProvedOddUnaryResidual
import Paper2.Paper1ProvedOddProvider

/-! Actual source access in the initial isotropic ordinary-unary arm.
The one-sided case is consumed by the proved EO reduction. Otherwise the
opposing original support produces a genuinely independent ordinary unary,
with an exact original-field installation. The residual isotropic pair is
recorded faithfully; no Z row or hardness assertion is manufactured. -/
namespace Paper2.Paper1Proved.OddUnary.Isotropic
open Paper2.Tractable Paper2.ExactInput
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace Ordinary
export GeneralOddUnaryOrdinary (pairing determinant escape_isotropic independent_of_isotropic isotropic_diagnostic pairing_diagnostic)
end Ordinary
namespace Frame
export GeneralOddNonisotropicFrame (norm)
end Frame
namespace Access
export GeneralOddHighTerminalAccess (Actual Reduction controlled)
end Access

 theorem norm_eq_pairing (u : Signature AlgebraicComplex 1) :
    Frame.norm u = Ordinary.pairing u u := by
  simp [Frame.norm,Ordinary.pairing,Holant.Signature.connect_equality,pow_two]

/-- Failure of common-side support produces an actual second ordinary graph;
its coefficients remain in the original G+Eq field and its installation
programme retains all original labels. -/
 theorem independent_second (L : Language)
    (U : Access.Actual (signatures L) 1) (hu : U.graph.denote ≠ 0)
    (hi : Frame.norm U.graph.denote = 0)
    (hs : ¬ CommonOneSided (kCoordinates L.family)) :
    ∃ V : Access.Actual (signatures L) 1,
      Ordinary.pairing U.graph.denote V.graph.denote ≠ 0 ∧
      Ordinary.determinant U.graph.denote V.graph.denote ≠ 0 ∧
      Nonempty (Access.Reduction (signatures L) V) := by
  have hi' : Ordinary.pairing U.graph.denote U.graph.denote = 0 := by
    simpa only [norm_eq_pairing] using hi
  have hs' : ¬ Holant.Tractable.CommonOneSided
      (Holant.Tractable.kCoordinates (GeneralOddUnarySource.original (signatures L))) := hs
  obtain ⟨N,hN,hE,hpair⟩ := Ordinary.escape_isotropic
    (GeneralOddUnarySource.original (signatures L)) U.graph U.uses U.ordinary hu hi' hs'
  let V : Access.Actual (signatures L) 1 := ⟨N,hN,hE⟩
  exact ⟨V,hpair,Ordinary.independent_of_isotropic _ _ hi' hpair,
    ⟨Access.controlled (signatures L) V⟩⟩

/-- The complete initial split consumes the common-side obstruction. The
other arm supplies independent physical unaries, rather than an unproved
hardness conclusion from their independence. -/
 theorem hard_or_independent (L : Language) (hp : Preprocessed L.family)
    (U : Access.Actual (signatures L) 1) (hu : U.graph.denote ≠ 0)
    (hi : Frame.norm U.graph.denote = 0) (hnot : ¬ Tract L.family) :
    FixedFieldOutput.SharpPHard .ordinary L ∨
      ∃ V : Access.Actual (signatures L) 1,
        Ordinary.pairing U.graph.denote V.graph.denote ≠ 0 ∧
        Ordinary.determinant U.graph.denote V.graph.denote ≠ 0 ∧
        Nonempty (Access.Reduction (signatures L) V) := by
  by_cases hs : CommonOneSided (kCoordinates L.family)
  · apply Or.inl
    apply OddProvider.ordinary_oneSided_failure_hard L hp hs
    intro he
    apply hnot
    unfold Tract
    rw [preprocess_eq_self hp]
    exact ⟨L.family_finite,Or.inl ⟨hs,he⟩⟩
  · exact Or.inr (independent_second L U hu hi hs)

/-- The produced second graph is either a genuine nonisotropic unary, or an
independent isotropic pair. This retains the exact remaining consumer arm. -/
 theorem hard_or_nonisotropic_or_pair (L : Language) (hp : Preprocessed L.family)
    (U : Access.Actual (signatures L) 1) (hu : U.graph.denote ≠ 0)
    (hi : Frame.norm U.graph.denote = 0) (hnot : ¬ Tract L.family) :
    FixedFieldOutput.SharpPHard .ordinary L ∨
      (∃ V : Access.Actual (signatures L) 1,
        Frame.norm V.graph.denote ≠ 0 ∧ Nonempty (Access.Reduction (signatures L) V)) ∨
      (∃ V : Access.Actual (signatures L) 1,
        Frame.norm V.graph.denote = 0 ∧
        Ordinary.pairing U.graph.denote V.graph.denote ≠ 0 ∧
        Ordinary.determinant U.graph.denote V.graph.denote ≠ 0 ∧
        Nonempty (Access.Reduction (signatures L) V)) := by
  rcases hard_or_independent L hp U hu hi hnot with hh | ⟨V,hpair,hdet,hred⟩
  · exact Or.inl hh
  · by_cases hn : Frame.norm V.graph.denote = 0
    · exact Or.inr (Or.inr ⟨V,hn,hpair,hdet,hred⟩)
    · exact Or.inr (Or.inl ⟨V,hn,hred⟩)

/-- Consume every nonisotropic second graph by the complete framed selector.
The remaining resources are a genuine prime ternary source or a pair of
independent isotropic original unaries. -/
 theorem hard_or_ternary_or_isotropic_pair
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (U : Access.Actual (signatures L) 1) (hu : U.graph.denote ≠ 0)
    (hi : Frame.norm U.graph.denote = 0) (hnot : ¬ Tract L.family) :
    FixedFieldOutput.SharpPHard .ordinary L ∨ Nonempty (TernarySource L) ∨
      (∃ V : Access.Actual (signatures L) 1,
        Frame.norm V.graph.denote = 0 ∧
        Ordinary.pairing U.graph.denote V.graph.denote ≠ 0 ∧
        Ordinary.determinant U.graph.denote V.graph.denote ≠ 0 ∧
        Nonempty (Access.Reduction (signatures L) V)) := by
  rcases hard_or_nonisotropic_or_pair L hp U hu hi hnot with hh | hv | hpair
  · exact Or.inl hh
  · obtain ⟨V,hn,_⟩ := hv
    rcases Source.hard_or_ternary L V hn hnot P PG PR PF PN with hh | ht
    · exact Or.inl hh
    · exact Or.inr (Or.inl ht)
  · exact Or.inr (Or.inr hpair)

end
end Paper2.Paper1Proved.OddUnary.Isotropic

