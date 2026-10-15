import Paper2.SourceFaithful.HeightTwo
import Paper2.SourceFaithful.GadgetAugmentation
import Paper2.SourceFaithful.Synthesis.SameGraph
import Paper2.Paper1ProvedNetwork
import Paper2.HeightOne.Cyclic.QuaternaryFourier
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpenAlgebra
import Holant.EightVertex.ProductAnchor.NetworksData

/-! A physical ordinary equality-four graph is a terminal without any free
binary resource.  Its inverse-K image is an actual native eight-vertex graph.
The proof uses the already proved height-two endpoint, which is independent
of the ordinary odd classification being completed here. -/
namespace Paper2.Paper1Proved.OddUnary
open Paper2.Tractable Paper2.ExactInput Paper2.Synthesis Paper2.HeightTwo
open Holant.LocalDrafts.RemoteWork.StableClosureV2
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The finite network records have the same ordered incidence data. -/
def importedNetwork {K : Type} {n : ℕ} (G : Holant.Network K n) : Paper2.Network K n :=
  ⟨⟨G.shape.vertices,G.shape.arity,G.shape.edges,G.shape.ports⟩,G.vertex,G.edge⟩

@[simp] theorem importedNetwork_denote {K : Type} [CommSemiring K] {n : ℕ}
    (G : Holant.Network K n) : (importedNetwork G).denote = G.denote := rfl

def nativeEqualityFour : Signature AlgebraicComplex 4 :=
  Paper2.Tractable.sourceKBasis.symm.action Holant.EightVertex.ProductAnchor.equalityFour

lemma equalityFour_points :
    (Holant.EightVertex.ProductAnchor.equalityFour : Signature AlgebraicComplex 4) =
      HeightOne.PhaseCards.point (fun _ => false) + HeightOne.PhaseCards.point (fun _ => true) := by
  funext x
  cases h : x 0 <;>
    simp [Holant.EightVertex.ProductAnchor.equalityFour,HeightOne.PhaseCards.point,
      Pi.add_apply,funext_iff,h]
  all_goals exact ⟨0,h⟩

lemma nativeEqualityFour_apply (x : Fin 4 → Bool) :
    nativeEqualityFour x =
      (∏ i, Paper2.Tractable.KInverse (x i) false) + (∏ i, Paper2.Tractable.KInverse (x i) true) := by
  rw [nativeEqualityFour,equalityFour_points]
  classical
  simp [Paper2.Tractable.InvertibleKernel.action,Paper2.Tractable.InvertibleKernel.symm,
    Paper2.Tractable.sourceKBasis,Paper2.Signature.coordinateAction,HeightOne.PhaseCards.point,
    mul_add,Finset.sum_add_distrib]

lemma nativeEqualityFour_eightVertex :
    EvenSupport nativeEqualityFour ∧ nativeEqualityFour (fun _ => false) ≠ 0 ∧
      nativeEqualityFour (fun _ => true) ≠ 0 := by
  have hc : ∀ x : Fin 4 → Bool, nativeEqualityFour x =
      Paper2.Tractable.KInverse (x 0) false * Paper2.Tractable.KInverse (x 1) false * Paper2.Tractable.KInverse (x 2) false * Paper2.Tractable.KInverse (x 3) false +
      Paper2.Tractable.KInverse (x 0) true * Paper2.Tractable.KInverse (x 1) true * Paper2.Tractable.KInverse (x 2) true * Paper2.Tractable.KInverse (x 3) true := by
    intro x
    rw [nativeEqualityFour_apply]
    simp [Fin.prod_univ_succ]
    ring
  have hw : ∀ x : Fin 4 → Bool, Paper2.weight x =
      (if x 0 then 1 else 0) + (if x 1 then 1 else 0) +
        (if x 2 then 1 else 0) + (if x 3 then 1 else 0) := by
    intro x
    simp only [Paper2.weight,Fin.sum_univ_four]
  have hi3 : Paper2.Tractable.imaginaryUnit ^ 3 = -Paper2.Tractable.imaginaryUnit := by
    calc
      _ = Paper2.Tractable.imaginaryUnit ^ 2 * Paper2.Tractable.imaginaryUnit := by ring
      _ = _ := by rw [Paper2.Tractable.imaginaryUnit_sq]; ring
  refine ⟨?_,?_,?_⟩
  · intro x hx
    rw [hc] at hx
    rw [hw]
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp only [h0,h1,h2,h3,Bool.false_eq_true,↓reduceIte,Nat.even_iff] at hx ⊢ <;>
      try norm_num
    all_goals exfalso; apply hx; simp only [Paper2.Tractable.KInverse,↓reduceIte]
    all_goals field_simp [Paper2.Tractable.sqrtTwo_ne_zero]
    all_goals ring_nf
    all_goals norm_num [hi3,neg_pow]
    all_goals ring_nf
    all_goals norm_num [Paper2.Tractable.imaginaryUnit_sq]
  · rw [hc]
    simp only [Paper2.Tractable.KInverse,↓reduceIte]
    have hi : Paper2.Tractable.imaginaryUnit ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by decide,pow_mul,Paper2.Tractable.imaginaryUnit_sq]; norm_num
    have hs : Paper2.Tractable.sqrtTwo ^ 4 = 4 := by rw [show (4 : ℕ) = 2 * 2 by decide,pow_mul,Paper2.Tractable.sqrtTwo_sq]; norm_num
    ring_nf
    norm_num [hi,← inv_pow,hs,Paper2.Tractable.sqrtTwo_ne_zero]
  · rw [hc]
    simp only [Paper2.Tractable.KInverse,↓reduceIte]
    have hi : Paper2.Tractable.imaginaryUnit ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 by decide,pow_mul,Paper2.Tractable.imaginaryUnit_sq]; norm_num
    have hs : Paper2.Tractable.sqrtTwo ^ 4 = 4 := by rw [show (4 : ℕ) = 2 * 2 by decide,pow_mul,Paper2.Tractable.sqrtTwo_sq]; norm_num
    ring_nf
    norm_num [hi,← inv_pow,hs,Paper2.Tractable.sqrtTwo_ne_zero]

/-- Inverse K transforms only labels; every original Eq wire becomes X. -/
theorem ordinary_network_inverseK (L : Language) {n : ℕ}
    (G : Holant.Network AlgebraicComplex n)
    (huses : ∀ v, (⟨G.shape.arity v,G.vertex v⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hordinary : ∀ e, G.edge e = Holant.Signature.equality) :
    NetworkRealizable (inverseKLanguage L).family (Paper2.Tractable.sourceKBasis.symm.action G.denote) := by
  let H := OpenHolographic.transform G Paper2.Tractable.KMatrix Paper2.Tractable.KInverse
  refine ⟨n,importedNetwork H,Equiv.refl _,?_,?_,?_⟩
  · intro v
    rw [inverseKLanguage_family]
    exact ⟨⟨G.shape.arity v,G.vertex v⟩,huses v,rfl⟩
  · intro e
    change Holant.Kernel.pullback (G.edge e) Paper2.Tractable.KMatrix = _
    rw [hordinary]
    exact Paper2.Tractable.sourceKBasis_pullback
  · change H.denote = Paper2.Tractable.sourceKBasis.symm.action G.denote
    exact OpenHolographic.denote_transform G Paper2.Tractable.KMatrix Paper2.Tractable.KInverse Paper2.Tractable.KMatrix_mul_inverse

/-- Canonical fixed-field hardness from an actual scalar ordinary Eq4 graph.
No odd-source theorem, physical X, physical Z, or implicit edge addition is used. -/
theorem ordinary_equalityFour_hard
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted)
    (L : Language) (hnot : ¬ Tract L.family)
    (G : Holant.Network AlgebraicComplex 4)
    (huses : ∀ v, (⟨G.shape.arity v,G.vertex v⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hordinary : ∀ e, G.edge e = Holant.Signature.equality)
    (c : AlgebraicComplex) (hc : c ≠ 0)
    (hform : G.denote = fun x => c * Holant.EightVertex.ProductAnchor.equalityFour x) :
    FixedFieldOutput.SharpPHard .ordinary L := by
  have hg := ordinary_network_inverseK L G huses hordinary
  have hscaled : Paper2.Tractable.sourceKBasis.symm.action G.denote = fun x => c * nativeEqualityFour x := by
    rw [hform]
    funext x
    simp only [nativeEqualityFour,Paper2.Tractable.InvertibleKernel.action,
      Paper2.Signature.coordinateAction,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring

  obtain ⟨H,hU,hX,hD⟩ := hg.ordered
  have hreal : NativeNetworkRealizesUpTo (inverseKLanguage L).family nativeEqualityFour :=
    ⟨H,hU,hX,c,hc,hD.trans hscaled⟩
  obtain ⟨M,hM,hred⟩ := PG.adjoin (inverseKLanguage L) nativeEqualityFour hreal
  obtain ⟨Q,hQ⟩ := Language.coverage_family (preprocess M.family)
    (M.family_finite.subset (fun _ h => h.1))
  obtain ⟨he,h0,h1⟩ := nativeEqualityFour_eightVertex
  have hp : Preprocessed Q.family := by rw [hQ]; exact preprocess_preprocessed _
  have hmem : (⟨4,nativeEqualityFour⟩ : AnySignature AlgebraicComplex) ∈ Q.family := by
    rw [hQ,hM]
    exact ⟨Set.mem_insert _ _,by decide,fun hz => h0 (congrFun hz _)⟩
  have hn : ¬ Tract (Paper2.kImage Q) := by
    intro ht
    have hm : Tract (Paper2.kImage M) := (kImage_preprocessed_tract_iff M Q hQ).mp ht
    apply hnot
    rw [← kImage_inverseKLanguage L]
    apply hm.mono_family (familyAction_mono Paper2.Tractable.sourceKBasis ?_)
    rw [hM]
    exact Set.subset_insert _ _
  have hh := (SourceFaithful.HeightTwo.eightVertex_classification_preprocessed P PF PN Q hp
    nativeEqualityFour hmem he h0 h1).resolve_left hn
  have hr := PR.restriction_2_5 Q M (by rw [hQ]; exact fun _ h => h.1)
  exact (SourceFaithful.Synthesis.ordinary_hard_iff_inverseK_native L).mpr
    (hh.transport (hr.trans hred))

end
end Paper2.Paper1Proved.OddUnary

