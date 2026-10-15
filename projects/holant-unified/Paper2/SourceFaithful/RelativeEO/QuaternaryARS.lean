import Paper2.SourceFaithful.RelativeEO.QuaternaryTerminal
import Paper2.SourceFaithful.RelativeEO.MatchingTerminal

namespace Paper2.SourceFaithful.RelativeEO
open Tractable ExactInput Paper2.RelativeEO

theorem quaternary_relative_terminal (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (f : Signature AlgebraicComplex 4)
    (hf : f ≠ 0) (he : Signature.CentralSupport f)
    (hmem : (⟨4,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hout : ¬ IsARSProduct f) : FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases hm : WeightedMatching.IsProduct f
  · exact matching_relative_terminal B F U L hpre hboth hnot f hmem hm hout
  · exact quaternary_nonmatching_terminal G O F U E R L hpre hboth hnot f hf he hmem hm

/-- The original ambient language is classified when the quaternary was
actually constructed, rather than already literally present. -/
theorem realized_quaternary_relative_terminal (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (f : Signature AlgebraicComplex 4)
    (hf : f ≠ 0) (he : Signature.CentralSupport f)
    (hgraph : NativeNetworkRealizesUpTo L.family f)
    (hout : ¬ IsARSProduct f) : FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨M,hM,hML⟩ := G.adjoin L f hgraph
  have hLM : L.family ⊆ M.family := by rw [hM]; exact Set.subset_insert _ _
  have hpreM : Preprocessed M.family := by
    intro g hg
    rw [hM] at hg
    rcases hg with rfl | hg
    · exact ⟨by change 0 < (4 : ℕ); decide,hf⟩
    · exact hpre g hg
  have hbothM : BothChargeSigns M.family := by
    obtain ⟨⟨f,hf,x,hx,hn⟩,⟨g,hg,y,hy,hp⟩⟩ := hboth
    exact ⟨⟨f,hLM hf,x,hx,hn⟩,⟨g,hLM hg,y,hy,hp⟩⟩
  have hnotM : ¬ Tract (kImage M) := fun ht =>
    hnot (ht.mono_family (familyAction_mono sourceKBasis hLM))
  exact (quaternary_relative_terminal G O F U E R B M hpreM hbothM hnotM f hf he
    (by rw [hM]; exact Set.mem_insert _ _) hout).transport hML


end Paper2.SourceFaithful.RelativeEO
