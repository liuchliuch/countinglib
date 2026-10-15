import Paper2.Paper1ProvedOddUnaryNRSupport
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Basic

/-! Reconstruction of the sheared tensor class from an explicit finite
partition of its support and the exact coefficient inheritance relations. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K] [CharZero K]

private def coordinateTag {n m : ℕ} (allowed : Fin n → Prop)
    (label : Fin n → Fin m) (i : Fin n) : Sum (Fin m) (Fin n) := by
  classical
  exact if allowed i then Sum.inl (label i) else Sum.inr i

private def Block {n m : ℕ} (allowed : Fin n → Prop) (label : Fin n → Fin m) :=
  {b : Sum (Fin m) (Fin n) // ∃ i, coordinateTag allowed label i = b}

private def Fiber {n m : ℕ} (allowed : Fin n → Prop) (label : Fin n → Fin m)
    (b : Block allowed label) := {i : Fin n // coordinateTag allowed label i = b.val}

private instance blockFintype {n m : ℕ} (allowed : Fin n → Prop) (label : Fin n → Fin m) :
    Fintype (Block allowed label) := by
  classical
  unfold Block
  infer_instance

private instance fiberFintype {n m : ℕ} (allowed : Fin n → Prop) (label : Fin n → Fin m)
    (b : Block allowed label) : Fintype (Fiber allowed label b) := by
  classical
  unfold Fiber
  infer_instance

private theorem tag_inl_iff {n m : ℕ} (allowed : Fin n → Prop)
    (label : Fin n → Fin m) (i : Fin n) (l : Fin m) :
    coordinateTag allowed label i=Sum.inl l ↔ allowed i ∧ label i=l := by
  classical
  by_cases h : allowed i <;> simp [coordinateTag,h]

private theorem tag_inr_iff {n m : ℕ} (allowed : Fin n → Prop)
    (label : Fin n → Fin m) (i j : Fin n) :
    coordinateTag allowed label i=Sum.inr j ↔ ¬allowed i ∧ i=j := by
  classical
  by_cases h : allowed i <;> simp [coordinateTag,h]

private def blockFin {n m : ℕ} (allowed : Fin n → Prop) (label : Fin n → Fin m) :
    Block allowed label ≃ Fin (Fintype.card (Block allowed label)) := by
  classical
  exact Fintype.equivFin _

private def fiberFin {n m : ℕ} (allowed : Fin n → Prop) (label : Fin n → Fin m)
    (b : Block allowed label) : Fiber allowed label b ≃ Fin (Fintype.card (Fiber allowed label b)) := by
  classical
  exact Fintype.equivFin _

private def partitionPorts {n m : ℕ} (allowed : Fin n → Prop) (label : Fin n → Fin m) :
    (Σ k : Fin (Fintype.card (Block allowed label)),
      Fin (Fintype.card (Fiber allowed label ((blockFin allowed label).symm k)))) ≃ Fin n := by
  classical
  exact (Equiv.sigmaCongr (blockFin allowed label).symm
    (fun k => (fiberFin allowed label ((blockFin allowed label).symm k)).symm)).trans
    (Equiv.sigmaSubtypeFiberEquiv (coordinateTag allowed label)
      (fun b => ∃ i, coordinateTag allowed label i = b) (fun i => ⟨i,rfl⟩))

private theorem partitionPorts_apply {n m : ℕ} (allowed : Fin n → Prop)
    (label : Fin n → Fin m) (k) (j) :
    partitionPorts allowed label ⟨k,j⟩ =
      ((fiberFin allowed label ((blockFin allowed label).symm k)).symm j).val := rfl

private theorem port_tag {n m : ℕ} (allowed : Fin n → Prop)
    (label : Fin n → Fin m) (k) (j) :
    coordinateTag allowed label (partitionPorts allowed label ⟨k,j⟩)=
      ((blockFin allowed label).symm k).val := by
  exact ((fiberFin allowed label ((blockFin allowed label).symm k)).symm j).property

private theorem fiber_positive {n m : ℕ} (allowed : Fin n → Prop)
    (label : Fin n → Fin m) (b : Block allowed label) :
    0 < Fintype.card (Fiber allowed label b) := by
  classical
  obtain ⟨i,hi⟩ := b.property
  exact Fintype.card_pos_iff.mpr ⟨⟨i,hi⟩⟩

private theorem fiber_pin_card {n m : ℕ} (allowed : Fin n → Prop)
    (label : Fin n → Fin m) (b : Block allowed label) (i : Fin n)
    (hb : b.val = Sum.inr i) : Fintype.card (Fiber allowed label b)=1 := by
  classical
  obtain ⟨a,ha⟩ := b.property
  have ai : a=i := by
    rw [hb] at ha
    exact ((tag_inr_iff allowed label a i).mp ha).2
  have only : ∀ z : Fiber allowed label b,z.val=i := by
    intro z
    have hz : coordinateTag allowed label z.val=Sum.inr i := z.property.trans hb
    exact ((tag_inr_iff allowed label z.val i).mp hz).2
  let e : Fiber allowed label b ≃ Fin 1 :=
    { toFun := fun _ => 0
      invFun := fun _ => ⟨a,ha⟩
      left_inv := fun z => Subtype.ext (ai.trans (only z).symm)
      right_inv := fun z => Fin.eq_zero z |>.symm }
  simpa using Fintype.card_congr e

private def partitionDecomposition {n m : ℕ} (allowed : Fin n → Prop)
    (label : Fin n → Fin m) (c : K) (hc : c≠0) : TensorDecomposition K n := by
  classical
  exact
    { count := Fintype.card (Block allowed label)
      arity := fun k => Fintype.card (Fiber allowed label ((blockFin allowed label).symm k))
      factor := fun k => match ((blockFin allowed label).symm k).val with
        | Sum.inl _ => row (1/2)
        | Sum.inr _ => pin 1
      ports := partitionPorts allowed label
      scale := Units.mk0 c hc }

omit [CharZero K] in
private theorem partition_generators {n m : ℕ} (allowed : Fin n → Prop)
    (label : Fin n → Fin m) (c : K) (hc : c≠0) (k) :
    Generator ((partitionDecomposition allowed label c hc).arity k)
      ((partitionDecomposition allowed label c hc).factor k) := by
  classical
  let b := (blockFin allowed label).symm k
  cases hb : b.val with
  | inl l =>
    exact Or.inr ⟨fiber_positive allowed label b,1/2,by simp [partitionDecomposition,b,hb]⟩
  | inr i =>
    exact Or.inl ⟨fiber_pin_card allowed label b i hb,1,by simp [partitionDecomposition,b,hb]⟩

private theorem partition_origin {n m : ℕ} (allowed : Fin n → Prop)
    (label : Fin n → Fin m) (c : K) (hc : c≠0) :
    (partitionDecomposition allowed label c hc).value (fun _ => false)=c := by
  classical
  unfold TensorDecomposition.value
  have factors : ∀ k,(partitionDecomposition allowed label c hc).factor k (fun _ => false)=1 := by
    intro k
    cases hb : ((blockFin allowed label).symm k).val <;>
      simp [partitionDecomposition,hb,row,pin,Holant.weight]
  simp only [factors,Finset.prod_const_one,mul_one]
  rfl

private theorem partition_live_iff {n m : ℕ} (allowed : Fin n → Prop)
    (label : Fin n → Fin m) (c : K) (hc : c≠0) (x : Fin n → Bool) :
    (partitionDecomposition allowed label c hc).value x≠0 ↔ Matches allowed label x := by
  classical
  let D := partitionDecomposition allowed label c hc
  have tag (k : Fin D.count) (j : Fin (D.arity k)) :
      coordinateTag allowed label (D.ports ⟨k,j⟩)=((blockFin allowed label).symm k).val :=
    port_tag allowed label k j
  have form (k : Fin D.count) : D.factor k=
      match ((blockFin allowed label).symm k).val with
      | Sum.inl _ => row (1/2)
      | Sum.inr _ => pin 1 := rfl
  change D.value x≠0 ↔ _
  rw [decomposition_live_iff]
  constructor
  · intro live
    have allow : ∀ i,x i=true → allowed i := by
      intro i xi
      rcases hi : D.ports.symm i with ⟨k,j⟩
      have ip : D.ports ⟨k,j⟩=i := by simpa only [hi] using D.ports.apply_symm_apply i
      have localLive := live k
      rw [form] at localLive
      cases hb : ((blockFin allowed label).symm k).val with
      | inl l =>
        exact ((tag_inl_iff allowed label i l).mp (by simpa [ip,hb] using tag k j)).1
      | inr a =>
        have all := (pin_live_iff (by norm_num : (1:K)≠0) _).mp (by simpa [hb] using localLive)
        have impossible := all j
        simp [ip,xi] at impossible
    refine ⟨allow,?_⟩
    intro i j ne xi xj equal
    rcases hi : D.ports.symm i with ⟨k,a⟩
    rcases hj : D.ports.symm j with ⟨l,b⟩
    have ip : D.ports ⟨k,a⟩=i := by simpa only [hi] using D.ports.apply_symm_apply i
    have jp : D.ports ⟨l,b⟩=j := by simpa only [hj] using D.ports.apply_symm_apply j
    have tags : coordinateTag allowed label i=coordinateTag allowed label j := by
      simp [coordinateTag,allow i xi,allow j xj,equal]
    have kl : k=l := by
      have vals : ((blockFin allowed label).symm k).val=((blockFin allowed label).symm l).val := by
        rw [←tag k a,←tag l b,ip,jp]
        exact tags
      exact (blockFin allowed label).symm.injective (Subtype.ext vals)
    subst l
    have localLive := live k
    rw [form] at localLive
    cases hb : ((blockFin allowed label).symm k).val with
    | inl t =>
      have unique := (row_live_iff (by norm_num : (1/2:K)≠0) _).mp (by simpa [hb] using localLive)
      have ab := unique a b (by simpa [ip] using xi) (by simpa [jp] using xj)
      exact ne (by rw [←ip,←jp,ab])
    | inr t =>
      have all := (pin_live_iff (by norm_num : (1:K)≠0) _).mp (by simpa [hb] using localLive)
      have impossible := all a
      simp [ip,xi] at impossible
  · rintro ⟨allow,distinct⟩ k
    rw [form]
    cases hb : ((blockFin allowed label).symm k).val with
    | inl t =>
      apply (row_live_iff (by norm_num : (1/2:K)≠0) _).mpr
      intro a b xa xb
      by_contra ab
      have ne : D.ports ⟨k,a⟩≠D.ports ⟨k,b⟩ := by
        intro eq
        exact ab (by simpa using D.ports.injective eq)
      have different := distinct _ _ ne xa xb
      have la := ((tag_inl_iff allowed label _ t).mp (by simpa [hb] using tag k a)).2
      have lb := ((tag_inl_iff allowed label _ t).mp (by simpa [hb] using tag k b)).2
      exact different (la.trans lb.symm)
    | inr t =>
      apply (pin_live_iff (by norm_num : (1:K)≠0) _).mpr
      intro j
      cases xj : x (D.ports ⟨k,j⟩)
      · rfl
      · have forbidden := ((tag_inr_iff allowed label _ t).mp (by simpa [hb] using tag k j)).1
        exact False.elim (forbidden (allow _ xj))

/-- Exact reconstruction: the finite support partition supplies the ordered
ports and literal generators; inheritance fixes every supported coefficient. -/
theorem closed_of_partition_support {n : ℕ} {f : Holant.Signature K n}
    (support : PartitionSupport f) (inherited : Inheritance f) : Closed f := by
  classical
  obtain ⟨m,allowed,label,support⟩ := support
  have origin : f (fun _ => false)≠0 := by
    apply (support _).mpr
    constructor
    · intro i hi
      cases hi
    · intro i j ne hi
      cases hi
  let D := partitionDecomposition allowed label (f (fun _ => false)) origin
  have hD : ∀ k,Generator (D.arity k) (D.factor k) :=
    partition_generators allowed label _ origin
  have di : Inheritance D.value := decomposition_inheritance D
    (fun k => generator_inheritance (hD k))
  refine Or.inr ⟨D,hD,?_⟩
  funext x
  by_cases live : f x≠0
  · have dlive : D.value x≠0 :=
      (partition_live_iff allowed label _ origin x).mpr ((support x).mp live)
    have fnormal := inheritance_normalizes inherited x live
    have dnormal := inheritance_normalizes di x dlive
    have d0 : D.value (fun _ => false)=f (fun _ => false) :=
      partition_origin allowed label _ origin
    rw [d0,←fnormal] at dnormal
    exact mul_left_cancel₀ (pow_ne_zero _ (by norm_num : (2:K)≠0)) dnormal
  · have dzero : D.value x=0 := by
      by_contra dlive
      exact live ((support x).mpr ((partition_live_iff allowed label _ origin x).mp dlive))
    exact dzero.trans (not_ne_iff.mp live).symm

end
end Paper2.Paper1Proved.OddUnary.NR

