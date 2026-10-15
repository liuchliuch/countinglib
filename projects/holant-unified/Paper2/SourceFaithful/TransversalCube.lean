import Paper2.TransversalCube
import Paper2.SourceFaithful.LocalInputs

/-! Source-faithful canonical-number-field hardness of the actual matching
mountain gadget. The finite graph and EOTract obstruction are independently
proved; only the explicitly authorized Paper1 EO/direct-gadget inputs occur. -/
namespace Paper2.SourceFaithful.TransversalCube
open Tractable ExactInput Paper2.TransversalCube
open scoped BigOperators
variable {n : ℕ}

theorem six_singleton_hard (EO : Paper1EOAccepted) (f : Signature AlgebraicComplex 4)
    (hf : ∀ x, f x ≠ 0 ↔ weight x = 2) :
    ∃ H : Language, H.family = {⟨4,f⟩} ∧ FixedFieldOutput.SharpPHard .nativeX H := by
  obtain ⟨H,hH⟩ := Language.coverage_family ({⟨4,f⟩} : SignatureFamily AlgebraicComplex)
    (Set.finite_singleton _)
  refine ⟨H,hH,(EO.eo_2_16 H ?_ ?_).2 ?_⟩
  · intro g hg
    rw [hH, Set.mem_singleton_iff] at hg
    subst g
    refine ⟨by change 0 < 4; decide, ?_⟩
    intro hz
    have hn := (hf ![false, false, true, true]).2 (by decide +kernel)
    exact hn (congrFun hz _)
  · intro g hg
    rw [hH,Set.mem_singleton_iff] at hg
    subst g
    exact six_isEO f hf
  · rw [hH]
    exact six_not_eoTract f hf

theorem matching_mountain_hard
    (DG : Paper1DirectGadgetAccepted) (R : Paper1RestrictionAccepted) (EO : Paper1EOAccepted)
    (L : Language) (P : WeightedMatching.Pairing n) (hd : 3 ≤ P.count)
    (a b c : AlgebraicComplex) (p q : Fin P.count → AlgebraicComplex) (hab : a*b ≠ 0)
    (hcoeff : c * ∏ j, p j * q j ≠ 0)
    (hM : (⟨n,sourceMountain P a b c p q⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨N,hU,hX,_,_,hs,_,_,_⟩ := exists_native_gadget P hd a b c p q hab hcoeff L.family hM
  have hreal : NativeNetworkRealizesUpTo L.family N.denote :=
    ⟨N,hU,hX,1,one_ne_zero,by simp⟩
  obtain ⟨A,hA,hAL⟩ := DG.adjoin L N.denote hreal
  obtain ⟨H,hH,hHard⟩ := six_singleton_hard EO N.denote hs
  have hHA : FixedFieldOutput.Reduces .nativeX H A := R.restriction_2_5 H A (by
    rw [hH,hA]
    exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  exact hHard.transport (hHA.trans hAL)

end Paper2.SourceFaithful.TransversalCube

