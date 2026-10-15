import Paper2.Paper1ProvedOddUnaryTernaryResidual
import Paper2.Paper1ProvedOddUnaryCapBasis
import Paper2.Paper1ProvedOddUnaryWTrace
import Holant.Proofs.Recognition.TensorDecisionMatching
import Holant.Proofs.Closure.ClosureFactorTreeFieldMap
import Holant.Tractable.Conformal.TensorAlternatives

/-! The whole-family obstruction selects a genuine original row and an exact
prime factor outside either chosen common matching orientation. The selected
factor retains its original coefficient field and saved tensor tree. This is
a mathematical source selector, with no hardness conclusion assumed. -/
namespace Paper2.Paper1Proved.OddUnary.WEscape
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.FinitePGL2.Stabilization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Every nullary or unary signature is in both oriented matching classes. -/
theorem matchingImage_tiny (opposite : Bool) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : n ≤ 1) : matchingImage opposite n f := by
  let B : InvertibleKernel := if opposite then sourceKBasis.comp bitFlipBasis else sourceKBasis
  refine ⟨B.symm.action f,?_,?_⟩
  · intro x hx
    have hw : Holant.weight x ≤ n := Holant.weight_le x
    change 1 < Holant.weight x at hx
    omega
  · change Signature.coordinateAction
      (fun _ => if opposite then Kernel.mul KMatrix Signature.disequality else KMatrix)
        (B.symm.action f)=f
    have hb : (fun _ : Fin n => if opposite then
        Kernel.mul KMatrix Signature.disequality else KMatrix)=(fun _ => B.matrix) := by
      funext i
      cases opposite <;> rfl
    rw [hb]
    exact B.action_symm_action f

/-- Multiplying by a nonzero scalar does not change matching-image membership. -/
theorem matchingImage_scale_iff (opposite : Bool) {n : ℕ}
    (f : Holant.Signature AlgebraicComplex n) (c : AlgebraicComplex) (hc : c ≠ 0) :
    matchingImage opposite n (fun x => c*f x) ↔ matchingImage opposite n f := by
  let B := Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionMatching.basis opposite
  have criterion (g : Holant.Signature AlgebraicComplex n) :
      matchingImage opposite n g ↔ Holant.Signature.OneHot (B.symm.action g) := by
    constructor
    · exact Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionMatching.inverse_factor opposite n g
    · intro h
      have hh := Holant.LocalDrafts.RemoteWork.TractChainV1.TensorDecisionMatching.forward_factor
        opposite n (B.symm.action g) h
      simpa only [B,InvertibleKernel.action_symm_action] using hh
  rw [criterion,criterion]
  have he : B.symm.action (fun x => c*f x)=fun x => c*(B.symm.action f) x :=
    ClosureFactorTreeAction.coordinateAction_scale _ f c
  rw [he]
  constructor
  · intro h x hx
    exact (mul_eq_zero.mp (h x hx)).resolve_left hc
  · intro h x hx
    simp [h x hx]

variable {r : ℕ} {b : ℕ → ℕ}
variable (K : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r) → Signature K (b i.val))

/-- Failure of the entire seven-alternative criterion supplies a retained
nonzero row outside each fixed matching orientation. -/
theorem outside_row
    (negative : ¬ Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (opposite : Bool) :
    ∃ i : Fin r, 0 < b i.val ∧ H i ≠ 0 ∧
      ¬ SourceTensorClosure (matchingImage opposite)
        (RingHomRealization.mapSignature K.subtype (H i)) := by
  classical
  by_contra none
  apply negative
  refine ⟨(Set.finite_range (fun i : Fin r =>
    (⟨b i.val,GlobalCloseCompletionUnaryDescentSource.mapped K H i⟩ :
      AnySignature AlgebraicComplex))).subset (fun _ h => h.1),?_⟩
  have hm : ∀ f ∈ preprocess (GlobalCloseCompletionUnaryDescentSource.ambient K H),
      SourceTensorClosure (matchingImage opposite) f.2 := by
    rintro f ⟨⟨i,rfl⟩,positive,nonzero⟩
    have hi : H i ≠ 0 := by
      intro hz
      apply nonzero
      funext x
      change K.subtype (H i x)=0
      simp [hz]
    by_contra hout
    exact none ⟨i,positive,hi,hout⟩
  apply Or.inr
  apply Or.inr
  apply Or.inr
  apply Or.inl
  cases opposite
  · exact Or.inl hm
  · exact Or.inr hm

/-- The offending row has an exact nonunary prime leaf in its original
coefficient field. Its mapped signature violates the chosen matching image. -/
theorem outside_prime_leaf
    (negative : ¬ Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (opposite : Bool) :
    ∃ i : Fin r, ∃ _positive : 0 < b i.val, ∃ nonzero : H i ≠ 0,
      ∃ g ∈ (GlobalCloseCompletionUnaryWholeFamilySelector.tree K H i nonzero).leaves,
        2 ≤ g.1 ∧ Prime g ∧
          ¬ matchingImage opposite g.1 (RingHomRealization.mapSignature K.subtype g.2) := by
  classical
  obtain ⟨i,positive,nonzero,outside⟩ := outside_row K H negative opposite
  let t := GlobalCloseCompletionUnaryWholeFamilySelector.tree K H i nonzero
  have found : ∃ g ∈ t.leaves,
      ¬ matchingImage opposite g.1 (RingHomRealization.mapSignature K.subtype g.2) := by
    by_contra none
    apply outside
    apply Or.inr
    have all : ∀ g ∈ t.leaves,
        matchingImage opposite g.1 (RingHomRealization.mapSignature K.subtype g.2) := by
      intro g hg
      by_contra bad
      exact none ⟨g,hg,bad⟩
    have ht := ClosureSmallArity.tensorClosure_of_saved_tree
      (ClosureFactorTreeFieldMap.tree K.subtype t) (matchingImage opposite)
      (fun g hg => by
        rw [ClosureFactorTreeFieldMap.leaves] at hg
        obtain ⟨v,hv,rfl⟩ := Multiset.mem_map.mp hg
        exact all v hv)
    have hmap : (Holant.LocalDrafts.FinitePGL2.Stabilization.mapSignature K.subtype
        (⟨b i.val,(GlobalCloseCompletionUnaryWholeFamilySelector.row K H i).network.denote⟩ :
          AnySignature K)).2 = RingHomRealization.mapSignature K.subtype
            (GlobalCloseCompletionUnaryWholeFamilySelector.row K H i).network.denote := rfl
    rw [hmap,GlobalCloseCompletionUnaryWholeFamilySelector.row_value] at ht
    exact ht
  obtain ⟨g,hg,bad⟩ := found
  refine ⟨i,positive,nonzero,g,hg,?_,t.leaves_prime g hg,bad⟩
  by_contra small
  exact bad (matchingImage_tiny opposite _ (by omega))

/-- Two independent actual unaries physically expose a prime graph violating
any chosen common matching orientation. Every vertex retains the same table. -/
theorem outside_prime_graph
    (negative : ¬ Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H))
    (opposite : Bool) (caps : Bool → NoXOrdinaryGraphAdjoin.Output H 1)
    (hd : CapBasis.determinant (fun v => (caps v).network.denote) ≠ 0) :
    ∃ n, 2 ≤ n ∧ ∃ V : NoXOrdinaryGraphAdjoin.Output H n,
      Prime (⟨n,V.network.denote⟩ : Holant.AnySignature K) ∧
      ¬ matchingImage opposite n (RingHomRealization.mapSignature K.subtype V.network.denote) := by
  obtain ⟨i,positive,nonzero,g,member,big,prime,bad⟩ :=
    outside_prime_leaf K H negative opposite
  let N := GlobalCloseCompletionUnaryWholeFamilySelector.row K H i
  obtain ⟨V,pv,c,hc,form⟩ := CapBasis.exists_leaf H caps N hd
    (by rwa [GlobalCloseCompletionUnaryWholeFamilySelector.row_value])
    (GlobalCloseCompletionUnaryWholeFamilySelector.tree K H i nonzero) g member
  refine ⟨g.1,big,V,pv,?_⟩
  have hm : RingHomRealization.mapSignature K.subtype V.network.denote=
      fun x => K.subtype c*RingHomRealization.mapSignature K.subtype g.2 x := by
    rw [form]
    funext x
    exact map_mul K.subtype c (g.2 x)
  rw [hm,matchingImage_scale_iff opposite _ (K.subtype c)
    (fun hz => hc (Subtype.ext hz))]
  exact bad

/-- The W packet itself supplies the independent cap basis, so its whole-family
obstruction exposes an actual original-table prime outside either orientation. -/
theorem residual_outside_prime_graph {L : Paper2.ExactInput.Language}
    (S : IsotropicWSource L) (opposite : Bool) :
    ∃ n, 2 ≤ n ∧ ∃ V : NoXOrdinaryGraphAdjoin.Output S.source.H n,
      Prime (⟨n,V.network.denote⟩ : Holant.AnySignature S.source.K) ∧
      ¬ matchingImage opposite n
        (RingHomRealization.mapSignature S.source.K.subtype V.network.denote) := by
  obtain ⟨Q,hq0,hq1,hnorm⟩ := WTrace.residual_unary S.source.K S.source.H S.residual
  let q : NoXOrdinaryGraphAdjoin.Output S.source.H 1 :=
    ⟨Q.network,Q.labels,Q.exact,Q.edges⟩
  let caps : Bool → NoXOrdinaryGraphAdjoin.Output S.source.H 1 :=
    fun v => if v then q else S.source.zeroPin
  have hd : CapBasis.determinant (fun v => (caps v).network.denote) ≠ 0 := by
    change S.source.zeroPin.network.denote (fun _ => false)*Q.network.denote (fun _ => true)-
      S.source.zeroPin.network.denote (fun _ => true)*Q.network.denote (fun _ => false) ≠ 0
    rw [S.source.zeroPinFalse,S.source.zeroPinTrue,zero_mul,sub_zero]
    exact mul_ne_zero S.source.scalarNonzero hq1
  exact outside_prime_graph S.source.K S.source.H S.source.negative opposite caps hd

end
end Paper2.Paper1Proved.OddUnary.WEscape
