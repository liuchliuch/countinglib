import Paper2.Paper1ProvedOddUnaryOneHotLineProjection
import Holant.Certificates.OctahedralSeparator.TensorTransport
import Mathlib.Data.Fintype.Prod

/-! At every arity, failure of one fixed matching orientation is visible
in a binary physical pin face along its unchanged original-field line. -/
namespace Paper2.Paper1Proved.OddUnary.OneHotLineVisibility
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.TractChainV1
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def appendEquiv (m : ℕ) : (Fin m→Bool)×(Fin 2→Bool)≃(Fin (m+2)→Bool) where
  toFun y:=Fin.append y.1 y.2
  invFun x:=(fun i=>x (Fin.castAdd 2 i),fun j=>x (Fin.natAdd m j))
  left_inv y:=by
    apply Prod.ext <;> funext i <;> simp
  right_inv x:=by
    funext i
    refine Fin.addCases (fun j=>?_) (fun j=>?_) i <;> simp

theorem action_append {m : ℕ} (R : InvertibleKernel)
    (f : Holant.Signature AlgebraicComplex (m+2)) (z : Fin m→Bool) :
    R.symm.action f (Fin.append z ![true,true])=
      ∑ y:Fin m→Bool,(∏i,R.symm.matrix (z i) (y i))*
        R.symm.action (kernelSignature (fun b c=>f (Fin.append y ![b,c]))) ![true,true] := by
  classical
  letI : Fintype ((Fin m→Bool)×(Fin 2→Bool)) := instFintypeProd _ _
  let E:=appendEquiv m
  unfold InvertibleKernel.action Holant.Signature.coordinateAction
  rw [←E.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro y _
  change (∑w:Fin 2→Bool,(∏i:Fin (m+2),
    R.symm.matrix (Fin.append z ![true,true] i) (Fin.append y w i))*f (Fin.append y w))=_
  simp only [Fin.prod_univ_add,Fin.append_left,Fin.append_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  have hw : (![w 0,w 1] : Fin 2→Bool)=w := by funext i;fin_cases i <;> rfl
  simp only [kernelSignature]
  rw [hw]
  ring

def last (m : ℕ) (b : Bool) : Fin (m+2) :=
  Fin.natAdd m (if b then 1 else 0 : Fin 2)

def pairOrder {m : ℕ} (i j : Fin (m+2)) : Equiv.Perm (Fin (m+2)) :=
  (Equiv.swap i (last m false)).trans
    (Equiv.swap ((Equiv.swap i (last m false)) j) (last m true))

theorem pairOrder_first {m : ℕ} (i j : Fin (m+2)) (hne : i≠j) :
    pairOrder i j i=last m false := by
  classical
  have h0 : (Equiv.swap i (last m false)) j≠last m false := by
    intro eqn
    have e : (Equiv.swap i (last m false)) j=(Equiv.swap i (last m false)) i := by
      simpa using eqn
    exact hne ((Equiv.swap i (last m false)).injective e).symm
  have h1 : last m false≠last m true := by
    intro eqn
    have e:=congrArg Fin.val eqn
    simp [last] at e
  simp only [pairOrder,Equiv.trans_apply,Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne h0.symm h1

theorem pairOrder_second {m : ℕ} (i j : Fin (m+2)) :
    pairOrder i j j=last m true := by
  classical
  simp only [pairOrder,Equiv.trans_apply,Equiv.swap_apply_left]

theorem high_word_pair {m : ℕ} (x : Fin (m+2)→Bool) (high : 1<Holant.weight x) :
    ∃p:Equiv.Perm (Fin (m+2)),∃z:Fin m→Bool,
      (fun i=>Fin.append z ![true,true] (p i))=x := by
  classical
  let s:=Finset.univ.filter (fun i:Fin (m+2)=>x i=true)
  have card : s.card=Holant.weight x := by
    simp only [s,Finset.card_eq_sum_ones,Finset.sum_filter,Holant.weight]
  obtain ⟨i,j,hi,hj,hne⟩:=Finset.one_lt_card_iff.mp (by rwa [card])
  have hxi : x i=true := (Finset.mem_filter.mp hi).2
  have hxj : x j=true := (Finset.mem_filter.mp hj).2
  let p:=pairOrder i j
  let z:Fin m→Bool:=fun k=>x (p.symm (Fin.castAdd 2 k))
  refine ⟨p,z,?_⟩
  have ei : p.symm (last m false)=i := p.symm_apply_eq.mpr (pairOrder_first i j hne).symm
  have ej : p.symm (last m true)=j := p.symm_apply_eq.mpr (pairOrder_second i j).symm
  funext k
  obtain ⟨q,rfl⟩:=p.symm.surjective k
  rw [Equiv.apply_symm_apply]
  refine Fin.addCases (fun k=>?_) (fun b=>?_) q
  · simp only [Fin.append_left,z]
  · fin_cases b
    · rw [Fin.append_right]
      change true=x (p.symm (last m false))
      rw [ei,hxi]
    · rw [Fin.append_right]
      change true=x (p.symm (last m true))
      rw [ej,hxj]

variable {K : Type} [Field K]

theorem line_eq_weighted (u : Bool→K) (D : Bool→Bool→K) :
    OneHotLineProjection.line u D=∑i:Bool,∑j:Bool,u i*u j*D i j := by
  simp only [OneHotLineProjection.line,LinearMap.coe_mk,AddHom.coe_mk,Fintype.sum_bool]
  ring

/-- The selected face uses only literal original coordinates. Its nonzero
measurement is an element of K, even though matching is checked in AC. -/
theorem visible_pair {m : ℕ} (phi : K→+* AlgebraicComplex)
    (f : Holant.Signature K (m+2)) (u : Bool→K) (opposite : Bool)
    (c : AlgebraicComplex) (cnz : c≠0)
    (form : ∀v,phi (u v)=c*(TensorDecisionMatching.basis opposite).matrix v false)
    (outside : ¬matchingImage opposite (m+2) (RingHomRealization.mapSignature phi f)) :
    ∃p:Equiv.Perm (Fin (m+2)),∃y:Fin m→Bool,
      OneHotLineProjection.line u
        (fun b d=>Tensor.reindex p f (Fin.append y ![b,d]))≠0 := by
  classical
  by_contra none
  push Not at none
  let R:=TensorDecisionMatching.basis opposite
  let F:=RingHomRealization.mapSignature phi f
  have hot : Holant.Signature.OneHot (R.symm.action F) := by
    intro x high
    obtain ⟨p,z,word⟩:=high_word_pair x high
    have faces : ∀y:Fin m→Bool,
        R.symm.action (kernelSignature (fun b d=>Tensor.reindex p F (Fin.append y ![b,d])))
          ![true,true]=0 := by
      intro y
      rw [WEscape.inverse_binary_entry]
      have hm:=OneHotLineProjection.mapped_line phi u
        (fun b d=>Tensor.reindex p f (Fin.append y ![b,d])) opposite c form
      rw [none p y,map_zero] at hm
      exact (mul_eq_zero.mp hm.symm).resolve_left (pow_ne_zero 2 cnz)
    have hzero : R.symm.action (Tensor.reindex p F) (Fin.append z ![true,true])=0 := by
      rw [action_append]
      apply Finset.sum_eq_zero
      intro y _
      rw [faces y,mul_zero]
    have commutes:=Holant.Certificates.OctahedralSeparator.reindex_action
      (fun _ : Fin (m+2)=>R.symm.matrix) p F
    have he : R.symm.action (Tensor.reindex p F)=Tensor.reindex p (R.symm.action F) :=
      commutes.symm
    rw [he] at hzero
    change (R.symm.action F) (fun i=>Fin.append z ![true,true] (p i))=0 at hzero
    rwa [word] at hzero
  apply outside
  have matched:=TensorDecisionMatching.forward_factor opposite (m+2) (R.symm.action F) hot
  simpa only [R,F,InvertibleKernel.action_symm_action] using matched

theorem visible_weighted_pair {m : ℕ} (phi : K→+* AlgebraicComplex)
    (f : Holant.Signature K (m+2)) (u : Bool→K) (opposite : Bool)
    (c : AlgebraicComplex) (cnz : c≠0)
    (form : ∀v,phi (u v)=c*(TensorDecisionMatching.basis opposite).matrix v false)
    (outside : ¬matchingImage opposite (m+2) (RingHomRealization.mapSignature phi f)) :
    ∃p:Equiv.Perm (Fin (m+2)),∃y:Fin m→Bool,
      (∑i:Bool,∑j:Bool,u i*u j*Tensor.reindex p f (Fin.append y ![i,j]))≠0 := by
  obtain ⟨p,y,live⟩:=visible_pair phi f u opposite c cnz form outside
  exact ⟨p,y,by rwa [line_eq_weighted] at live⟩

end
end Paper2.Paper1Proved.OddUnary.OneHotLineVisibility

