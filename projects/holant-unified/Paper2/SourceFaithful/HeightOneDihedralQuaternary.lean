import Paper2.HeightOne.Dihedral.QuaternaryPrime
import Paper2.HeightOne.PhaseCards.Paper1Pencil
import Paper2.SourceFaithful.HeightOneWalshEquality

/-! The actual prime-quaternary branch of height-one odd-dihedral
classification, with the exact Paper 1 pencil proof instantiated and with
canonical answers in the original language's fixed number field. -/
namespace Paper2.SourceFaithful.HeightOne
noncomputable section
open Tractable ExactInput
open Paper2.HeightOne.PhaseCards Paper2.HeightOne.Dihedral
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup

/-- An actual tensor-prime quaternary in the complete safe odd-dihedral
transfer group gives the whole-language terminal. The complete pencil deck,
Walsh support form and actual root-phase dressing are proved internally. -/
theorem dihedral_prime_quaternary_classification
    (P : Paper1Accepted) (PG : Paper1DirectGadgetAccepted)
    (PR : Paper1RestrictionAccepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) (L : Language) (hpre : Preprocessed L.family)
    {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (hG : actualClasses L.family = dihedralPhaseClasses N)
    (hsafe : AllBinariesSafe L.family)
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable L.family f)
    (hp : TensorPrime f) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨a, p, r, hp0, hr, he⟩ :=
    actual_prime_quaternary_twoPoint provedPhasePencil hN hodd hG hsafe f hf hp
  obtain ⟨C⟩ := rotationCards_nonempty (Or.inr hG)
  exact walsh_quaternary_equality_classification P PG PR PF PN L hpre (by omega)
    C f hf a p r hp0 hr (Holant.Projective.CyclicPhasePencil.root_ne_zero (by omega) hr) he

end
end Paper2.SourceFaithful.HeightOne

