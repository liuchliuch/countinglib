import Paper2.DegreeCSP.QuarticLiftInstanceOrdered
import Paper2.DegreeCSP.QuarticLiftRawLookup
import Paper2.DegreeCSP.QuarticLiftInstanceRawCore
import Holant.Complexity.ClosedNetworkSemantics

/-! Exact incidence semantics of the deterministic quartic-lift raw emitter. -/
namespace Paper2.DegreeCSP.QuarticLiftInstance
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (α : Type) : DecidableEq α := Classical.decEq α
local instance (priority := 3000) : DecidableEq Bool := Bool.decEq

abbrev sourcePorts (r : QuarticLiftLayout.Input) :
    Ports (Fin r.val.vertices.length) (Fin r.val.edges.length) :=
  (Equiv.sigmaEquivProd (Fin r.val.vertices.length) (Fin 4)).symm.trans
    (r.val.portEquiv r.property)

theorem sourcePort_eq (r : QuarticLiftLayout.Input)
    (v : Fin r.val.vertices.length) (i : Fin 4) :
    QuarticLiftLayout.sourcePort ⟨r,v⟩ i.val =
      ((sourcePorts r (v,i)).1.val,(sourcePorts r (v,i)).2) := by
  change (r.val.vertices.get v).2.getD i.val (0,false) =
    r.val.portEndpoint r.property ⟨v,i⟩
  unfold Holant.Complexity.RawClosedNetwork.portEndpoint
  exact List.getD_eq_get (r.val.vertices.get v).2 (0,false) (Fin.cast (r.property.1 v).2.symm i)

@[simp] theorem scopeAddress_eq (P : Presentation AlgebraicComplex (Fin 2))
    (r : QuarticLiftLayout.Input) (v : Fin r.val.vertices.length)
    (w : Fin 2 ⊕ Fin P.hiddenCount) :
    QuarticLiftLayout.scopeAddress P ⟨r,v⟩ w =
      (variableIndex P r.val.vertices.length r.val.edges.length
        (embed P (sourcePorts r) v w)).val := by
  cases w with
  | inl i =>
    change QuarticLiftLayout.endpointAddress (QuarticLiftLayout.sourcePort ⟨r,v⟩ (mainPort i).val) = _
    rw [sourcePort_eq r v (mainPort i)]
    exact (variableIndex_endpoint_val P _ _ (sourcePorts r (v,mainPort i)).1
      (sourcePorts r (v,mainPort i)).2).symm
  | inr h =>
    change QuarticLiftLayout.hiddenAddress P ⟨r,v⟩ h = _
    exact (variableIndex_hidden_val P _ _ v h).symm

@[simp] theorem pairPort_val (i j : Fin 2) : (pairPort i j).val = 2*i.val+j.val := by
  fin_cases i <;> fin_cases j <;> rfl

@[simp] theorem endpoint_local_eq (P : Presentation AlgebraicComplex (Fin 2))
    (r : QuarticLiftLayout.Input) (v : Fin r.val.vertices.length) (i j : Fin 2) :
    QuarticLiftLayout.endpointAddress (QuarticLiftLayout.sourcePort ⟨r,v⟩ (2*i.val+j.val)) =
      (variableIndex P r.val.vertices.length r.val.edges.length
        (addedScope P (sourcePorts r) (Sum.inl (v,i)) j)).val := by
  rw [← pairPort_val,sourcePort_eq]
  exact (variableIndex_endpoint_val P _ _ (sourcePorts r (v,pairPort i j)).1
    (sourcePorts r (v,pairPort i j)).2).symm


abbrev rawTag (P : Presentation AlgebraicComplex (Fin 2))
    (r : QuarticLiftLayout.Input) (k : ℕ) :=
  Tag P (Fin r.val.vertices.length) (Fin r.val.edges.length) k

def rawFactorEquiv (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (r : QuarticLiftLayout.Input) :
    rawTag P r k ≃ Fin (QuarticLiftLayout.raw P labels k label r).factors.length :=
  (constraintIndex P r.val.vertices.length r.val.edges.length k).trans
    (finCongr (QuarticLiftLayout.factors_length P labels k label r).symm)

abbrev rawLabel (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (label : ℕ) {r : QuarticLiftLayout.Input} {k : ℕ} :
    rawTag P r k → ℕ
  | Sum.inl c => labels c.2
  | Sum.inr _ => label

abbrev rawScope (P : Presentation AlgebraicComplex (Fin 2))
    (r : QuarticLiftLayout.Input) {k : ℕ} (c : rawTag P r k) (j : Fin (arity P c)) :
    Fin (2*r.val.edges.length+r.val.vertices.length*P.hiddenCount) :=
  variableIndex P r.val.vertices.length r.val.edges.length (coreScope P (sourcePorts r) c j)

theorem rawFactor_eq (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (r : QuarticLiftLayout.Input)
    (c : rawTag P r k) :
    (QuarticLiftLayout.raw P labels k label r).factors.get (rawFactorEquiv P labels k label r c) =
      (rawLabel P labels label c,List.ofFn (fun j => (rawScope P r c j).val)) := by
  change (QuarticLiftLayout.factors P labels k label r).get
    (QuarticLiftLayout.factorIndex P labels k label r c) = _
  rcases c with ⟨v,c⟩ | ⟨(⟨v,i⟩ | e),q⟩
  · rw [QuarticLiftLayout.factors_get_old]
    apply Prod.ext
    · rfl
    apply congrArg List.ofFn
    funext j
    exact scopeAddress_eq P r v (P.scope c j)
  · rw [QuarticLiftLayout.factors_get_local]
    apply Prod.ext
    · rfl
    simp only [List.ofFn_succ,List.ofFn_zero]
    apply congrArg₂ List.cons
    · exact endpoint_local_eq P r v i 0
    apply congrArg₂ List.cons
    · exact endpoint_local_eq P r v i 1
    rfl
  · rw [QuarticLiftLayout.factors_get_outer]
    apply Prod.ext
    · rfl
    simp only [List.ofFn_succ,List.ofFn_zero]
    simp [QuarticLiftLayout.outerFactor,rawScope,coreScope,scope,addedScope,endBit]


theorem rawDegree_eq (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (r : QuarticLiftLayout.Input)
    (i : Fin (QuarticLiftLayout.raw P labels k label r).variables) :
    Raw.degree (QuarticLiftLayout.raw P labels k label r) i.val =
      (ordered P (sourcePorts r) k).degree i := by
  rw [raw_degree_scope _ (arity P) (rawFactorEquiv P labels k label r)
    (rawLabel P labels label) (rawScope P r) (rawFactor_eq P labels k label r),
    instance_degree_natCard]
  let ve := variableIndex P r.val.vertices.length r.val.edges.length
  let w := ve.symm i
  have hi : i=ve w := (ve.apply_symm_apply i).symm
  rw [hi]
  refine Nat.card_congr ((Equiv.subtypeEquivRight ?_).trans
    (enumeratedFiber P (sourcePorts r) k ve
      (constraintIndex P r.val.vertices.length r.val.edges.length k) w).symm)
  intro o
  exact ve.injective.eq_iff

theorem rawValid (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (r : QuarticLiftLayout.Input)
    {s : ℕ} {a : ℕ → ℕ} (hlabels : ∀ c,labels c<s)
    (harities : ∀ c,a (labels c)=P.arity c) (hlabel : label<s) (hXarity : a label=2)
    (hP : P.DegreeDivisible k) :
    Raw.Valid s a k (QuarticLiftLayout.raw P labels k label r) := by
  refine ⟨?_,?_,?_⟩
  · intro c
    obtain ⟨t,rfl⟩ := (rawFactorEquiv P labels k label r).surjective c
    rw [rawFactor_eq]
    simp only [List.length_ofFn]
    cases t with
    | inl t => exact ⟨hlabels t.2,(harities t.2).symm⟩
    | inr t => exact ⟨hlabel,hXarity.symm⟩
  · intro p
    let pe := rawPortEquiv (QuarticLiftLayout.raw P labels k label r) (arity P)
      (rawFactorEquiv P labels k label r)
      (fun c => by rw [rawFactor_eq]; exact List.length_ofFn)
    obtain ⟨⟨c,j⟩,rfl⟩ := pe.surjective p
    rw [rawPort_address _ (arity P) (rawFactorEquiv P labels k label r)
      (rawLabel P labels label) (rawScope P r) (rawFactor_eq P labels k label r)]
    exact (rawScope P r c j).isLt
  · intro i hi
    rw [rawDegree_eq P labels k label r (⟨i,hi⟩)]
    exact ordered_divisible P (sourcePorts r) hP ⟨i,hi⟩


theorem sourceNetwork_value (r : QuarticLiftLayout.Input)
    (g : Signature AlgebraicComplex 2) :
    (network (sourcePorts r) g).denote Fin.elim0 =
      (r.val.realize r.property
        (fun _ => Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore.lift g)
        (fun _ => Signature.disequality)).denote Fin.elim0 := by
  unfold FiniteNetwork.denote Holant.Network.denote
  refine Finset.sum_congr ?_ ?_
  · ext z; simp
  intro z _
  rfl

end
end Paper2.DegreeCSP.QuarticLiftInstance
