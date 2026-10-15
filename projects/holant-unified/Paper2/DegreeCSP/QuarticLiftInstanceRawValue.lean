import Paper2.DegreeCSP.QuarticLiftInstanceRaw

/-! The exact ordered raw query has the same partition as its finite
occurrence presentation and the original opposite-pair lift graph. -/
namespace Paper2.DegreeCSP.QuarticLiftInstance
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
attribute [local instance] Classical.propDecidable
local instance rawValueDecidableEq (α : Type) : DecidableEq α := Classical.decEq α
local instance (priority := 3000) rawValueBoolDecidableEq : DecidableEq Bool := Bool.decEq

variable (P : Presentation AlgebraicComplex (Fin 2))
variable (labels : Fin P.constraints→ℕ) (k label : ℕ)
variable {s : ℕ} {a : ℕ→ℕ}
variable (hlabels : ∀ c,labels c<s) (harities : ∀ c,a (labels c)=P.arity c)
variable (hlabel : label<s) (hXarity : a label=2) (hP : P.DegreeDivisible k)

def rawInput (r : QuarticLiftLayout.Input) : Raw.Input s a k :=
  ⟨QuarticLiftLayout.raw P labels k label r,
    rawValid P labels k label r hlabels harities hlabel hXarity hP⟩

def rawTypedLabel (r : QuarticLiftLayout.Input) : rawTag P r k→Fin s
  | .inl c => ⟨labels c.2,hlabels c.2⟩
  | .inr _ => ⟨label,hlabel⟩

variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (hlitOld : ∀ c,(⟨a (labels c),G ⟨labels c,hlabels c⟩⟩ :
  AnySignature AlgebraicComplex)=⟨P.arity c,P.constraint c⟩)
variable (hlitX : (⟨a label,G ⟨label,hlabel⟩⟩ : AnySignature AlgebraicComplex)=
  ⟨2,kernelSignature Signature.disequality⟩)

include hlitOld hlitX in
theorem rawInput_partition (r : QuarticLiftLayout.Input) :
    Raw.value G (rawInput P labels k label hlabels harities hlabel hXarity hP r)=
      (ordered P (sourcePorts r) k).partition := by
  have hrow (c : rawTag P r k) :
      (QuarticLiftLayout.raw P labels k label r).factors.get
        (rawFactorEquiv P labels k label r c)=
      ((rawTypedLabel P labels k label hlabels hlabel r c).val,
        List.ofFn (fun j=>(rawScope P r c j).val)) := by
    cases c <;> exact rawFactor_eq P labels k label r _
  have hlit (c : rawTag P r k) :
      (⟨a (rawTypedLabel P labels k label hlabels hlabel r c).val,
        G (rawTypedLabel P labels k label hlabels hlabel r c)⟩ : AnySignature AlgebraicComplex)=
      ⟨arity P c,table P c⟩ := by
    cases c with
    | inl c => exact hlitOld c.2
    | inr c => exact hlitX
  unfold rawInput
  rw [raw_value_named G (QuarticLiftLayout.raw P labels k label r)
    (rawValid P labels k label r hlabels harities hlabel hXarity hP)
    (arity P) (rawFactorEquiv P labels k label r)
    (rawTypedLabel P labels k label hlabels hlabel r) (rawScope P r) (table P) hrow hlit]
  unfold Instance.partition
  refine Finset.sum_congr ?_ ?_
  · ext x
    simp only [Finset.mem_univ]
  intro x _
  let ce := constraintIndex P r.val.vertices.length r.val.edges.length k
  unfold Instance.weight Instance.route
  exact (ce.symm.prod_comp (fun c=>table P c (fun j=>x (rawScope P r c j)))).symm

include hlitOld hlitX in
theorem rawValue (r : QuarticLiftLayout.Input) {g : Signature AlgebraicComplex 2}
    (hPg : P.value=g) (hk : 0<k) :
    Raw.value G (rawInput P labels k label hlabels harities hlabel hXarity hP r)=
      (r.val.realize r.property
        (fun _=>Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore.lift g)
        (fun _=>Signature.disequality)).denote Fin.elim0 :=
  (rawInput_partition P labels k label hlabels harities hlabel hXarity hP G hlitOld hlitX r).trans
    ((ordered_partition P (sourcePorts r) hPg hk).trans (sourceNetwork_value r g))

end
end Paper2.DegreeCSP.QuarticLiftInstance
