import Paper2.SourceFaithful.HeightOneIteration
import Paper2.SourceFaithful.HeightOneDihedralQuaternary
import Paper2.HeightOne.Cyclic.HigherCollapse
import Paper2.HeightOne.Dihedral.SixPortActual
import Paper2.SourceFaithful.CyclicQuaternary
import Paper2.HeightOne.PhaseCards.Paper1Diagonal

/-! Analytic consequences of the actual stable normalized stage. The least
arity is realized by a literal retained prime, and both menus are the actual
representatives saturated by the source iteration. -/
namespace Paper2.SourceFaithful.HeightOne
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Tractable ExactInput
open Paper2.HeightOne Paper2.HeightOne.PhaseCards Paper2.HeightOne.Cyclic
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

namespace StableNormalizedStage

lemma prime_witness {L : Language} (S : StableNormalizedStage L) :
    ∃ f : Signature AlgebraicComplex S.minArity,
      (⟨S.minArity,f⟩ : AnySignature AlgebraicComplex) ∈ S.language.family ∧ TensorPrime f := by
  obtain ⟨⟨n,f⟩,hf,hp,hn,_⟩ := S.least.1
  dsimp only at hn
  subst n
  exact ⟨f,hf,hp⟩

lemma even_minArity {L : Language} (S : StableNormalizedStage L) : Even S.minArity := by
  obtain ⟨f,hf,_⟩ := S.prime_witness
  exact S.even ⟨S.minArity,f⟩ hf

/-- The cyclic higher collapse is applied to the exact rotation deck retained
by the iteration, so its arity conclusion concerns the actual current prime. -/
theorem cyclic_minArity_eq_four (PD : Paper1DiagonalSlicesAccepted)
    {L : Language} (S : StableNormalizedStage L)
    (hG : actualClasses S.language.family = cyclicPhaseClasses S.N) : S.minArity = 4 := by
  letI : NeZero S.N := ⟨by have := S.order_ge_three; omega⟩
  obtain ⟨f,hf,hp⟩ := S.prime_witness
  have hprocessed := S.rotations_processed ⟨S.minArity,f⟩ hf
  change (rotationMenu S.rotations).Processed ⟨S.minArity,f⟩ S.language at hprocessed
  exact minimum_cyclic_prime_arity_four PD S.rotations S.language S.order_ge_three
    S.even S.safe hG S.least f hf hp hprocessed

/-- The exceptional six-port base is eliminated by its complete actual xor
deck, including the order-three phase case. -/
theorem dihedral_minArity_ne_six {L : Language} (S : StableNormalizedStage L)
    (hG : actualClasses S.language.family = dihedralPhaseClasses S.N) : S.minArity ≠ 6 := by
  intro hn
  letI : NeZero S.N := ⟨by have := S.order_ge_three; omega⟩
  obtain ⟨X,hX⟩ := S.xor_cards hG
  have hw := S.prime_witness
  rw [hn] at hw
  obtain ⟨f,hf,hp⟩ := hw
  have hmin : LeastPrimeArity S.language.family 6 := by simpa only [hn] using S.least
  have hprocessed := hX ⟨6,f⟩ hf
  change (xorMenu X).Processed ⟨6,f⟩ S.language at hprocessed
  exact Paper2.HeightOne.Dihedral.minimum_six_not_tensorPrime X S.language S.order_ge_three
    S.even S.safe hG hmin f hprocessed hp

theorem dihedral_quaternary_terminal
    (P : Paper1Accepted) (PG : Paper1DirectGadgetAccepted)
    (PR : Paper1RestrictionAccepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) {L : Language} (S : StableNormalizedStage L)
    (hG : actualClasses S.language.family = dihedralPhaseClasses S.N)
    (hn : S.minArity = 4) : Terminal L := by
  obtain ⟨f,hf,hp⟩ := S.prime_witness
  revert f hf hp
  rw [hn]
  intro f hf hp
  exact S.terminal (dihedral_prime_quaternary_classification P PG PR PF PN S.language
    S.retained.preprocessed S.order_ge_three S.odd_order hG S.safe f
    (networkRealizable_of_mem hf) hp)

/-- The complete cyclic stable branch: the original prime is first proved
four-ary, then the genuine dressed four-port classification is invoked. -/
theorem cyclic_terminal
    (P : Paper1Accepted) (PG : Paper1DirectGadgetAccepted)
    (PR : Paper1RestrictionAccepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) {L : Language} (S : StableNormalizedStage L)
    (hG : actualClasses S.language.family = cyclicPhaseClasses S.N) : Terminal L := by
  have hn := S.cyclic_minArity_eq_four provedDiagonalSlices hG
  have hw := S.prime_witness
  rw [hn] at hw
  obtain ⟨f,hf,hp⟩ := hw
  exact S.terminal (cyclic_prime_quaternary_classification P PG PR PF PN S.language
    S.retained.preprocessed S.order_ge_three S.odd_order hG S.safe f
    (networkRealizable_of_mem hf) hp)

end StableNormalizedStage
end
end Paper2.SourceFaithful.HeightOne

