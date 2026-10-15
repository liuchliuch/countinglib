import Paper2.HeightOne.Dihedral.HighArityOrder
import Paper2.HeightOne.Dihedral.HighArityTagsSix

/-! The actual retained-menu bridge to every signed matching localization
instruction. Each scalar root is encoded as an element of the original
roots-of-unity group, preserving the exact coefficient and ordered ports. -/
namespace Paper2.HeightOne.Dihedral
noncomputable section
open Cyclic Tractable ExactInput PhaseCards GroupSplit
open HighArity
set_option backward.isDefEq.respectTransparency false
variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]

theorem minimum_signed_first_cards (C : XorCards F N) (L : Language)
    (heven : ∀ f ∈ L.family,Even f.1) (hsafe : AllBinariesSafe L.family)
    {r : ℕ} (hG : actualClasses L.family = dihedralPhaseClasses N)
    (hmin : LeastPrimeArity L.family (2*r+6))
    (f : Signature AlgebraicComplex (2*r+6))
    (hprocessed : (xorMenu C).Processed ⟨2*r+6,f⟩ L) :
    ∀ i : HighArity.PhaseLabel N,∀ p : Equiv.Perm (Fin (2*r+6)),
      Holant.Certificates.MatchingContractionClosure.MatchingOrZero monomialGroup
        (Holant.Signature.contract (phaseKernel i)
          (Tensor.reindex p.symm (walshCoordinates f))) := by
  intro i p
  let s : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq i.2.val i.2.property
  simpa only [s,rootsOfUnity.coe_mkOfPowEq,phaseKernel] using
    minimum_ordered_xor_matching C L heven hsafe hG hmin f hprocessed p i.1 s

end
end Paper2.HeightOne.Dihedral
