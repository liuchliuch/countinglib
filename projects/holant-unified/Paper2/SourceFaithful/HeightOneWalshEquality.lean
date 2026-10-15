import Paper2.HeightOne.Cyclic.ActualDressing
import Paper2.HeightOne.Cyclic.QuaternaryFourier
import Paper2.SourceFaithful.HeightTwo
import Paper2.SourceFaithful.GadgetAugmentation

/-! An actual four-port Walsh generalized equality whose complementary ratio
is an available root phase is a whole-language terminal. A single actual
rotation attachment equalizes its two coefficients; the resulting native
eight-vertex signature is classified with canonical fixed-field answers. -/
namespace Paper2.HeightOne.PhaseCards
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Tractable Dihedral Cyclic HeightTwo

lemma balanced_twoPoint_action (a : Fin 4 → Bool) (c : AlgebraicComplex)
    (x : Fin 4 → Bool) :
    action walsh (fun y => c * twoPoint a 1 y) x =
      c * ((∏ i : Fin 4, walsh (x i) (a i)) +
        (∏ i : Fin 4, walsh (x i) (!(a i)))) := by
  simp only [twoPoint, one_smul]
  rw [action_scalar, action_add]
  simp only [Pi.add_apply, action_point]

lemma walsh_complement_columns (x a : Fin 4 → Bool) :
    (∏ i, walsh (x i) (!(a i))) =
      (-1 : AlgebraicComplex) ^ weight x * ∏ i, walsh (x i) (a i) := by
  have h := walsh_complement_product a x
  convert h using 1
  · apply Finset.prod_congr rfl
    intro i _
    cases hx : x i <;> cases ha : a i <;> rfl
  · congr 1
    apply Finset.prod_congr rfl
    intro i _
    cases hx : x i <;> cases ha : a i <;> rfl

lemma balanced_twoPoint_eightVertex (a : Fin 4 → Bool) (c : AlgebraicComplex)
    (hc : c ≠ 0) :
    EvenSupport (action walsh (fun y => c * twoPoint a 1 y)) ∧
      action walsh (fun y => c * twoPoint a 1 y) (fun _ => false) ≠ 0 ∧
      action walsh (fun y => c * twoPoint a 1 y) (fun _ => true) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    apply Nat.even_iff.mpr
    by_contra hn
    have hp : weight x % 2 = 1 := by
      have h := Nat.mod_lt (weight x) (by decide : 0 < 2)
      omega
    apply hx
    rw [balanced_twoPoint_action, walsh_complement_columns,
      neg_one_pow_eq_pow_mod_two, hp]
    ring
  · rw [balanced_twoPoint_action]
    simpa [walsh] using mul_ne_zero hc (by norm_num : (2 : AlgebraicComplex) ≠ 0)
  · rw [balanced_twoPoint_action, walsh_complement_columns]
    have hw : weight (fun _ : Fin 4 => true) = 4 := by simp [weight]
    rw [hw]
    norm_num
    refine ⟨hc, ?_⟩
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    cases ha : a i <;> norm_num [walsh, ha]

end
end Paper2.HeightOne.PhaseCards

namespace Paper2.SourceFaithful.HeightOne
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Tractable ExactInput
open Paper2.HeightOne.PhaseCards Paper2.HeightOne.Dihedral Paper2.HeightOne.Cyclic
open Paper2.HeightOne.GroupSplit Paper2.HeightOne.GroupSplit.MatrixGroup
open Paper2.HighHeightNormalization
open Paper2.HeightTwo

/-- The real root-phase binary acts on one original port; its nonzero scale
is retained in both the Walsh coefficient identity and the exact-input gadget. -/
theorem walsh_twoPoint_root_eightVertex {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hN : 0 < N) (C : RotationCards F N) (f : Signature AlgebraicComplex 4)
    (hf : NetworkRealizable F f) (a : Fin 4 → Bool) (p r : AlgebraicComplex)
    (hp : p ≠ 0) (hr : r ^ N = 1) (hr0 : r ≠ 0)
    (hform : walshCoordinates f = fun x => p * twoPoint a r x) :
    ∃ g : Signature AlgebraicComplex 4, NetworkRealizable F g ∧
      EvenSupport g ∧ g (fun _ => false) ≠ 0 ∧ g (fun _ => true) ≠ 0 := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let α : AlgebraicComplex := if a 0 then r else r⁻¹
  have hα : α ^ N = 1 := by
    unfold α
    split
    · exact hr
    · rw [inv_pow, hr, inv_one]
  let R : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq α hα
  let g := attachment (0 : Fin 4) (C.binary R) f
  have hg : NetworkRealizable F g :=
    attachment_realizable_inputs 0 (C.binary R) f hf (C.actual R).1
  let m : AlgebraicComplex := if a 0 then r else 1
  let c := C.scale R * p * m
  have hm : m ≠ 0 := by unfold m; split <;> simp_all
  have hc : c ≠ 0 := mul_ne_zero (mul_ne_zero (C.scale_ne_zero R) hp) hm
  have hwalsh : walshCoordinates g = fun x => c * twoPoint a 1 x := by
    dsimp only [g]
    rw [cyclic_attachment_walsh 0 f (C.transfer_eq R), hform]
    funext x
    have hna := (sector_distinct 0 a).1
    change a ≠ (fun i => !(a i)) at hna
    by_cases hxa : x = a
    · subst x
      cases ha : a 0 <;> simp [twoPoint, point, hna, c, m, R, α, ha] <;> ring
    by_cases hxb : x = (fun i => !(a i))
    · subst x
      change (fun i => !(a i)) ≠ a at hxa
      cases ha : a 0 <;>
        simp [twoPoint, point, hxa, c, m, R, α, ha] <;>
        field_simp [hr0] <;> ring
    · simp [twoPoint, point, hxa, hxb]
  have he : g = action walsh (fun x => c * twoPoint a 1 x) := by
    rw [← hwalsh]
    exact (walsh_action_cancel g).symm
  obtain ⟨heven, hzero, hone⟩ := balanced_twoPoint_eightVertex a c hc
  exact ⟨g, hg, by simpa only [he] using heven,
    by simpa only [he] using hzero, by simpa only [he] using hone⟩

/-- Canonical-output whole-language terminal for an actual four-port Walsh
generalized equality with an available complementary root ratio. -/
theorem walsh_quaternary_equality_classification
    (P : Paper1Accepted) (PG : Paper1DirectGadgetAccepted)
    (PR : Paper1RestrictionAccepted) (PF : Paper1FactorClosureAccepted)
    (PN : Paper1NormalizationAccepted) (L : Language) (hpre : Preprocessed L.family)
    {N : ℕ} (hN : 0 < N) (C : RotationCards L.family N) (f : Signature AlgebraicComplex 4)
    (hf : NetworkRealizable L.family f) (a : Fin 4 → Bool) (p r : AlgebraicComplex)
    (hp : p ≠ 0) (hr : r ^ N = 1) (hr0 : r ≠ 0)
    (hform : walshCoordinates f = fun x => p * twoPoint a r x) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨g, hg, heven, hzero, hone⟩ :=
    walsh_twoPoint_root_eightVertex hN C f hf a p r hp hr hr0 hform
  obtain ⟨M, hM, hML, _⟩ := PG.adjoin_equivalence PR L g
    (NativeNetworkRealizesUpTo.of_realizable hg)
  have hsub : L.family ⊆ M.family := by rw [hM]; exact Set.subset_insert _ _
  have hpreM : Preprocessed M.family := by
    intro k hk
    rw [hM] at hk
    rcases hk with rfl | hk
    · exact ⟨by change 0 < (4 : ℕ); decide, fun hz => hzero (congrFun hz _)⟩
    · exact hpre k hk
  have hmem : (⟨4, g⟩ : AnySignature AlgebraicComplex) ∈ M.family := by
    rw [hM]
    exact Set.mem_insert _ _
  rcases SourceFaithful.HeightTwo.eightVertex_classification_preprocessed P PF PN M hpreM
    g hmem heven hzero hone with ht | hh
  · exact Or.inl (ht.mono_family (familyAction_mono sourceKBasis hsub))
  · exact Or.inr (hh.transport hML)

end
end Paper2.SourceFaithful.HeightOne

