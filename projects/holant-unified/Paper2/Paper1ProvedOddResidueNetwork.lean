import Paper2.Paper1ProvedNetwork
import Paper2.SourceFaithful.RelativeEO.DirectedPairFactors
import Holant.Proofs.Hardness.GeneralOddHigherResidueQuaternaryPinOrDEQ

/-! Literal original-network receipts for the nonprimitive ordinary odd
residue. The source theorem supplies only an actual directed pair or the
alternating EO copy table; no hardness consumer is assumed by this bridge. -/
namespace Paper2.Paper1Proved.OddResidue
noncomputable section
open Paper2.Tractable Paper2.ExactInput
set_option backward.isDefEq.respectTransparency false
namespace Odd
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnarySource (original)
end Odd
namespace Pin
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddHigherResidueQuaternaryPinOrDEQ
  (PinOrDEQ source)
end Pin

/-- The reverse network dictionary copies every vertex, edge and original
boundary incidence. It makes no field or graph-resource extension. -/
def fromSource {K : Type} {n : ℕ} (N : Holant.Network K n) : Paper2.Network K n :=
  ⟨⟨N.shape.vertices,N.shape.arity,N.shape.edges,N.shape.ports⟩,N.vertex,N.edge⟩

@[simp] theorem fromSource_denote {K : Type} [CommSemiring K] {n : ℕ}
    (N : Holant.Network K n) : (fromSource N).denote = N.denote := rfl

theorem fromSource_realizable {n : ℕ} (F : SignatureFamily AlgebraicComplex)
    (N : Holant.Network AlgebraicComplex n)
    (hF : Holant.Complexity.BinaryInterpolation.Chains.Uses N F)
    (hX : Holant.Complexity.BinaryInterpolation.Chains.Native N) :
    NetworkRealizable F N.denote := by
  exact ⟨n,fromSource N,Equiv.refl _,hF,hX,rfl⟩

@[simp] theorem original_family (L : Language) :
    Odd.original (signatures L) = L.family := rfl

@[simp] theorem source_kFamily (L : Language) :
    Holant.Tractable.kCoordinates (Odd.original (signatures L)) = kCoordinates L.family := rfl

/-- Actual nonprimitive odd residue resources on the exact inverse-K chart.
The scalar remains part of the table until genuine gadget installation. -/
theorem source_resources (L : Language) (j : Fin L.count)
    (hj : Odd (L.arity j.val)) (hjn : L.signature j ≠ 0)
    (hs : ¬ CommonOneSided (kCoordinates L.family))
    (hd : 3 ≤ Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddResidueGcd.supportGcd
      (signatures L)) :
    (∃ c : AlgebraicComplex,c ≠ 0 ∧ NetworkRealizable (kCoordinates L.family)
      (c • Paper2.RelativeEO.directedPair)) ∨
    (∃ c : AlgebraicComplex,c ≠ 0 ∧ NetworkRealizable (kCoordinates L.family)
      (c • Holant.LocalDrafts.RemoteWork.HardnessChainV1.ExactTwoSignatures.E)) := by
  have hs' : ¬ Holant.Tractable.CommonOneSided
      (Holant.Tractable.kCoordinates (Odd.original (signatures L))) := by
    rw [source_kFamily]
    exact hs
  rcases Pin.source (signatures L) j hj hjn hs' hd with h | h
  · obtain ⟨N,hN,hX,c,hc,hv⟩ := h
    refine Or.inl ⟨c,hc,?_⟩
    have hreal := fromSource_realizable _ N hN hX
    rw [source_kFamily,hv] at hreal
    exact hreal
  · obtain ⟨N,hN,hX,c,hc,hv⟩ := h
    refine Or.inr ⟨c,hc,?_⟩
    have hreal := fromSource_realizable _ N hN hX
    rw [source_kFamily,hv] at hreal
    exact hreal

end
end Paper2.Paper1Proved.OddResidue
