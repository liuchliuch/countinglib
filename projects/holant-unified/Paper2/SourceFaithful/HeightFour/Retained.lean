import Paper2.SourceFaithful.HeightFour.Complete
import Paper2.SourceFaithful.HighHeightCompleteNormalization

/-! The height-four endpoint on the exact finite normalization output. The
complete mountain, all original labels, every charge promise and the actual
backward reduction are retained; no separate atlas conclusion is supplied. -/
namespace Paper2.SourceFaithful.HeightFour
open Tractable ExactInput HighHeight BellReduction

theorem retained_normalized_mountain_hard
    (P : Paper1Accepted) (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (N : Paper1NormalizationAccepted)
    (L : Language) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (W : NormalizedMountain L 4) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  have hbothS : BothChargeSigns W.stage.language.family := by
    obtain ⟨⟨f,hf,x,hx,hn⟩,⟨g,hg,y,hy,hp⟩⟩ := hboth
    exact ⟨⟨f,W.stage.contains hf,x,hx,hn⟩,⟨g,W.stage.contains hg,y,hy,hp⟩⟩
  have hHighS : HighCharge W.stage.language.family := fun f hf =>
    ⟨W.stage.even f hf,W.stage.divisible f hf⟩
  have hM : ∀ x, W.mountain x =
      (if x = (fun _ => false) then W.leftEndpoint else 0) +
      (if x = (fun _ => true) then W.rightEndpoint else 0) + W.central x := by
    intro x
    exact congrFun W.decomposition x
  exact (normalized_mountain_hard P G O F U E R N W.stage.language W.stage.preprocessed
    hbothS hHighS (W.stage.nontractable hnot) W.mountain W.central
    W.leftEndpoint W.rightEndpoint W.endpoint_ne_zero W.central_eo
    W.coefficient W.matching W.deck W.coefficient_ne_zero hM W.member).transport W.stage.backward

end Paper2.SourceFaithful.HeightFour
