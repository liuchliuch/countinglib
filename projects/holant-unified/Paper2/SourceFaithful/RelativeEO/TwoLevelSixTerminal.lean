import Paper2.SourceFaithful.RelativeEO.RealizedTerminal
import Paper2.RelativeEO.TwoLevelSix

/-! Complete native-X hardness exit for the literal six-port Reed–Muller
endpoint-repair gadget. This avoids the arbitrary non-ARS descent: one actual
extra self-loop handles every ratio except the explicitly real exceptional
ratio, where the checked projective-ARS terminal applies to the original output. -/
namespace Paper2.SourceFaithful.RelativeEO
open Tractable ExactInput Paper2.RelativeEO ReedMullerNormalization

/-- Closing the first ordered pair retains every original source vertex and
adds exactly one native-X edge. -/
theorem twoLevelQuad_realizable (A B c : AlgebraicComplex)
    (L : Language) (hgraph : NetworkRealizable L.family (sixOutput A B c)) :
    NetworkRealizable L.family (twoLevelQuad A B c) := by
  obtain ⟨N,hN,hX,hf⟩ := hgraph.ordered
  refine ⟨4,N.contract Signature.disequality,Equiv.refl _,hN.contract _,hX.contract,?_⟩
  change (N.contract Signature.disequality).denote = twoLevelQuad A B c
  rw [Network.denote_contract,hf]
  rfl

/-- Every nontrivial endpoint imbalance gives original-language hardness,
using only exact Paper 1 records and concrete algebraic native-X networks. -/
theorem sixOutput_hard (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (A B c : AlgebraicComplex)
    (hc : c ≠ 0) (hab : A*B ≠ c^2)
    (hgraph : NetworkRealizable L.family (sixOutput A B c)) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases hdet : (A*B+3*c^2)^2 = (4*c^2)^2
  · have hars := sixOutput_exceptional_projectiveARS A B c hc
      (twoLevelQuad_exceptional_ratio A B c hab hdet)
    exact realized_ars_relative_terminal G O F U E R L hpre hboth hnot
      (sixOutput A B c) (by decide) (sixOutput_ne_zero A B c hc)
      (sixOutput_centralSupport A B c) hars
      (NativeNetworkRealizesUpTo.of_realizable hgraph)
      (fun hs => sixOutput_not_weightedMatching A B c hc hab hs.isProduct)
  · obtain ⟨N,hN,_,hpreN,hbothN,hnotN,hNL⟩ := retained_output G L hpre hboth hnot
      (twoLevelQuad A B c) (by decide) (twoLevelQuad_ne_zero A B c hc)
      (NativeNetworkRealizesUpTo.of_realizable (twoLevelQuad_realizable A B c L hgraph))
    exact (quaternary_nonmatching_terminal G O F U E R N hpreN hbothN hnotN
      (twoLevelQuad A B c) (twoLevelQuad_ne_zero A B c hc) (twoLevelQuad_central A B c)
      (by rw [hN]; exact Set.mem_insert _ _)
      (twoLevelQuad_not_matching A B c hc hdet)).transport hNL

end Paper2.SourceFaithful.RelativeEO
