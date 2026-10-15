import Paper2.DegreeCSP.ComputationRecords

/-! A stable occurrence ordinal is computed by an actual double scan of all
original rows and ports. Repeated addresses remain separate occurrences, and
only earlier occurrences of the same variable contribute a quotient token. -/
namespace Paper2.DegreeCSP.ComputationRecords.Ordinal
open Holant Holant.Algebraic Holant.Complexity Computability
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.Complexity.GraphPreprocessing Holant.Complexity.GraphPreprocessing.OriginalCoefficient
open Holant.Complexity.FixedGadgetSubstitution Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Program
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
def before (r : Raw) (p q : r.Ports) : Prop :=
  p.1.val<q.1.val ∨ (p.1.val=q.1.val ∧ p.2.val<q.2.val)
instance (r : Raw) : DecidableRel (before r) := fun p q => by unfold before; infer_instance
theorem asymmetric (r : Raw) : ∀p q,before r p q → ¬before r q p := by
  intro p q hp hq
  unfold before at *
  omega
theorem portList_sorted (r : Raw) : r.portList.Pairwise (before r) := by
  simp only [Paper2.DegreeCSP.Raw.portList, Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.portList]
  apply List.pairwise_flatMap.mpr
  constructor
  · intro v hv
    apply List.pairwise_map.mpr
    exact (List.pairwise_lt_finRange _).imp (fun {j k} h => Or.inr ⟨rfl,h⟩)
  · apply (List.pairwise_lt_finRange _).imp
    intro v w hvw p hp q hq
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hp
    obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hq
    exact Or.inl hvw
theorem grouping_count (r : Raw) (p : r.Ports) :
    (Raw.occurrences r (Raw.address r p)).idxOf p=
      ∑v : Fin r.factors.length,∑j : Fin (r.factors.get v).2.length,
        if r.address ⟨v,j⟩=r.address p ∧ before r ⟨v,j⟩ p then 1 else 0 := by
  have h := Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Program.Ordinal.sorted_filter_index (before r) (asymmetric r) r.portList
    (portList_sorted r) (fun q => r.address q==r.address p) p
    (r.portList_complete p) (by simp)
  change (r.portList.filter _).idxOf p=_
  rw [h]
  simp only [Paper2.DegreeCSP.Raw.portList, Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.portList]
  rw [List.filter_flatMap,List.length_flatMap]
  have count {D : Type} (xs : List D) (test : D → Bool) :
      (xs.filter test).length=(xs.map (fun b => if test b then 1 else 0)).sum := by
    induction xs with
    | nil => rfl
    | cons b bs ih => cases h : test b <;> simp [h,ih,Nat.add_comm]
  simp_rw [List.filter_map,List.length_map,count]
  simp only [Function.comp_def,id_eq,←List.ofFn_eq_map,List.sum_ofFn,beq_iff_eq,Bool.and_eq_true,decide_eq_true_eq]

def computes : Computes (Ports.encoding) UnaryBinary.unaryEncoding
    (fun p => (Raw.occurrences p.1.1 (Raw.address p.1.1 (Ports.rawPort p))).idxOf (Ports.rawPort p)) := by
  let ec := Ports.encoding
  let src : Ports.Input → Raw := fun p => p.1.1
  let ctx := Traversal.contextComputes ec src
  let selected := Traversal.selectedPortComputes ec src (Ports.sourceComputes)
  let qaddr := selected.andThen (Ports.addressComputes)
  let paddr := ctx.andThen (Ports.addressComputes)
  let qrow := (Traversal.rowIndexComputes ec src).andThen UnaryBinary.computes
  let prow := (ctx.andThen (Ports.rowIndexComputes)).andThen UnaryBinary.computes
  let qslot := (Traversal.portIndexComputes ec src).andThen UnaryBinary.computes
  let pslot := (ctx.andThen (Ports.indexComputes)).andThen UnaryBinary.computes
  let same := Arithmetic.equal qaddr paddr
  let prior := Boolean.combine Bool.or (Arithmetic.less qrow prow)
    (Boolean.combine Bool.and (Arithmetic.equal qrow prow) (Arithmetic.less qslot pslot))
  let test := Boolean.combine Bool.and same prior
  exact congrComputes (Traversal.count ec src (Ports.sourceComputes) _ test)
    (fun p => by
      rw [grouping_count]
      apply Finset.sum_congr rfl
      intro v hv
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Function.comp_def,id_eq,Ordinal.before,Traversal.original,Traversal.selectedPort,Ports.rawPort,
        Traversal.selected,Raw.address,decide_eq_true_eq,Bool.and_eq_true,Bool.or_eq_true]
      rfl)

end
end Paper2.DegreeCSP.ComputationRecords.Ordinal
