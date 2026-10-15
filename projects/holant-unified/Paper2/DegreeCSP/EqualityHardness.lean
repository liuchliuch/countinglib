import Paper2.DegreeCSP.OriginalBOComplete
import Paper2.DegreeCSP.BooleanHardness
import Paper2.Tractable.Downward

/-! Literal equality of any arity at least three and both literal native pins
give canonical counting hardness outside the original tractability criterion.
The proved degree-generated BO classification supplies the obstruction, and
the genuine equality gadget and controlled compiler remove auxiliary X. -/
namespace Paper2.DegreeCSP.EqualityHardness
open Tractable TensorDecomposition ExactInput Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem hard (L : Language) (k : ℕ) (hk : 3≤k)
    (heq : (⟨k,equality k⟩ : AnySignature AlgebraicComplex)∈L.family)
    (hp0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex)∈L.family)
    (hp1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex)∈L.family)
    (hnot : ¬Tract (familyAction sourceKBasis L.family)) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  let M := DisequalitySource.language L k hk heq
  have hsub : L.family⊆M.family := by
    rw [DisequalitySource.family]
    exact Set.subset_insert _ _
  have hx : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈M.family := by
    rw [DisequalitySource.family]
    exact Set.mem_insert _ _
  have hbad : ¬OriginalBO.AllGeneratedOriginalBO M.family k := by
    intro hBO
    have ht := OriginalBOComplete.tract_family M.family M.family_finite
      (by omega : 2≤k) hx (hsub hp0) (hsub hp1) hBO
    exact hnot (ht.mono_family (familyAction_mono sourceKBasis hsub))
  have hm := BooleanHardness.hard_of_not_allBO_withX M k hx hk
    (hsub heq) (hsub hp0) (hsub hp1) hbad
  intro count hcount
  obtain ⟨r⟩ := hm count hcount
  exact ⟨r.controlledCompose (DisequalitySource.back L k hk heq)⟩

end
end Paper2.DegreeCSP.EqualityHardness
