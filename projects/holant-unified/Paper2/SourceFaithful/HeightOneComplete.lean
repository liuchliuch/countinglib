import Paper2.SourceFaithful.HeightOneStableAnalytic
import Paper2.HeightOne.Dihedral.HighArityComplete
import Paper2.HeightOne.GroupSplit.Paper1Proved
import Paper2.Paper1ProvedUnaryProvider

/-! Complete source height-one mountain classification. Actual finite menu
saturation, the fixed original-field bound and strictly decreasing updates
produce the stable stage internally. Both complete analytic group branches
then classify the original canonical fixed-field counting problem. -/
namespace Paper2.SourceFaithful.HeightOne
noncomputable section
open Tractable ExactInput
open Paper2.HeightOne Paper2.HeightOne.PhaseCards Paper2.HeightOne.Cyclic
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup
set_option backward.isDefEq.respectTransparency false

namespace StableNormalizedStage

theorem dihedral_minArity_eq_four {L : Language} (S : StableNormalizedStage L)
    (hG : actualClasses S.language.family = dihedralPhaseClasses S.N) : S.minArity = 4 := by
  letI : NeZero S.N := ⟨by have := S.order_ge_three; omega⟩
  have hsmall : S.minArity < 8 := by
    by_contra hn
    obtain ⟨X,hX⟩ := S.xor_cards hG
    obtain ⟨f,hf,hp⟩ := S.prime_witness
    have hprocessed := hX ⟨S.minArity,f⟩ hf
    change (xorMenu X).Processed ⟨S.minArity,f⟩ S.language at hprocessed
    exact Paper2.HeightOne.Dihedral.minimum_higher_not_tensorPrime X S.language
      S.order_ge_three S.even S.safe (by omega) hG S.least f hprocessed hp
  have hn6 := S.dihedral_minArity_ne_six hG
  have hn3 := Paper2.HeightOne.LeastPrimeArity.ge_three S.least
  obtain ⟨k,hk⟩ := S.even_minArity
  omega

/-- No conditional stable-case conclusion remains: its actual cyclic or
dihedral group always leads to the canonical terminal for the original input. -/
theorem classification
    (P : Paper1Accepted) (PG : Paper1DirectGadgetAccepted)
    (PR : Paper1RestrictionAccepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) {L : Language} (S : StableNormalizedStage L) : Terminal L := by
  rcases S.group with hc | hd
  · exact S.cyclic_terminal P PG PR PF PN hc
  · exact S.dihedral_quaternary_terminal P PG PR PF PN hd (S.dihedral_minArity_eq_four hd)

end StableNormalizedStage

/-- Source height-one theorem for the whole preprocessed input language.
Every remaining parameter is an exact named upstream Paper 1 theorem with
the actual canonical output protocol. In particular there is no saturation,
successful-update, deck, bounded-prime, or analytic terminal assumption. -/
theorem mountain_classification_preprocessed
    (P : Paper1Accepted) (PG : Paper1DirectGadgetAccepted)
    (PR : Paper1RestrictionAccepted) (PF : Paper1FactorClosureAccepted)
    (PI : Paper1BinaryInterpolationAccepted) (PO : Paper1OddAccepted)
    (PN : Paper1NormalizationAccepted) (L : Language) (hpre : Preprocessed L.family)
    (f : Signature AlgebraicComplex 2) (hf : IsMountain (d:=1) f)
    (hmem : (⟨2,f⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  cases iteration_reaches_stable P provedPaper1 PG PR PF
      (Paper2.Paper1Proved.unaryProviderOfOdd PO PR) PI PO PN L hpre f hf hmem with
  | inl ht => exact ht
  | inr hS =>
    obtain ⟨S⟩ := hS
    exact S.classification P PG PR PF PN

end
end Paper2.SourceFaithful.HeightOne

