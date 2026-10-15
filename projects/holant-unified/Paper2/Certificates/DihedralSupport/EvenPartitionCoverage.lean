module
public import Paper2.Certificates.DihedralSupport.EvenPartitionCosets
public import Paper2.Certificates.DihedralSupport.Semantics
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Completeness of the thirty-one literal even partitions of six ports.
The input is an arbitrary actual partition into nonempty even blocks. The
cardinality argument bounds its number of blocks before the small exact
two-block and matching checks are used. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport
open scoped BigOperators

def blockPorts (b : Nat) : Finset (Fin 6) :=
  Finset.univ.filter (fun k=>b.testBit (5-k.val)=true)

def blockMask (b : Finset (Fin 6)) : Nat := index6 (fun k=>decide (k∈b))

theorem blockMask_lt (b : Finset (Fin 6)) : blockMask b<64 := index6_lt _

@[simp] theorem blockPorts_blockMask (b : Finset (Fin 6)) : blockPorts (blockMask b)=b := by
  ext k
  simp only [blockPorts,Finset.mem_filter,Finset.mem_univ,true_and]
  change word6 (index6 (fun k=>decide (k∈b))) k=true ↔ k∈b
  rw [word6_index6]
  simp

@[simp] theorem blockPorts_63 : blockPorts 63=Finset.univ := by decide +kernel

/-- Actual blocks partition all six ports, without a choice of labels/order. -/
def EvenPartition (B : Finset (Finset (Fin 6))) : Prop :=
  (∀b∈B,b.Nonempty) ∧ (∀b∈B,Even b.card) ∧
  (∀b∈B,∀c∈B,b≠c → Disjoint b c) ∧ B.biUnion id=Finset.univ

instance (B : Finset (Finset (Fin 6))) : Decidable (EvenPartition B) := by
  unfold EvenPartition
  infer_instance

theorem EvenPartition.block_card_ge_two {B : Finset (Finset (Fin 6))}
    (h : EvenPartition B) {b : Finset (Fin 6)} (hb : b∈B) : 2≤b.card := by
  have hp := Finset.card_pos.mpr (h.1 b hb)
  obtain ⟨k,hk⟩ := h.2.1 b hb
  omega

theorem EvenPartition.sum_card {B : Finset (Finset (Fin 6))}
    (h : EvenPartition B) : ∑b∈B,b.card=6 := by
  have hd : (B : Set (Finset (Fin 6))).PairwiseDisjoint id := h.2.2.1
  change ∑b∈B,(id b).card=6
  rw [←Finset.card_biUnion hd,h.2.2.2]
  simp

theorem EvenPartition.card_bound {B : Finset (Finset (Fin 6))}
    (h : EvenPartition B) : 0<B.card ∧ B.card≤3 := by
  have hn : B.Nonempty := by
    have hi : (0 : Fin 6)∈B.biUnion id := by rw [h.2.2.2]; simp
    obtain ⟨b,hb,_⟩ := Finset.mem_biUnion.mp hi
    exact ⟨b,hb⟩
  have hm : ∑b∈B,2≤∑b∈B,b.card := Finset.sum_le_sum (fun b hb=>h.block_card_ge_two hb)
  rw [h.sum_card] at hm
  have hm' : 2*B.card≤6 := by simpa [mul_comm] using hm
  exact ⟨Finset.card_pos.mpr hn,by omega⟩

def partitionCovered (B : Finset (Finset (Fin 6))) : Bool :=
  evenPartitions.any (fun bs=>decide (B=bs.toFinset.image blockPorts))

theorem partitionCovered_sound (B : Finset (Finset (Fin 6)))
    (h : partitionCovered B=true) :
    ∃bs∈evenPartitions,B=bs.toFinset.image blockPorts := by
  obtain ⟨bs,hbs,he⟩ := List.any_eq_true.mp h
  exact ⟨bs,hbs,of_decide_eq_true he⟩

/- Only 64² mask pairs are considered; the input remains the actual
nonempty/disjoint/even/covering partition predicate. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem two_blocks_covered : ∀a b : Fin 64,
    EvenPartition {blockPorts a.val,blockPorts b.val} →
    partitionCovered {blockPorts a.val,blockPorts b.val}=true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pair_mask_mem : ∀a : Fin 64,(blockPorts a.val).card=2 → a.val∈pairBlocks := by
  decide +kernel

def matchingCoverageCheck (a b c : Nat) : Bool :=
  decide (EvenPartition {blockPorts a,blockPorts b,blockPorts c} →
    partitionCovered {blockPorts a,blockPorts b,blockPorts c}=true)

/- The 15³ exact checks range over pair indicators, not over support masks or
an assumed list of actual partitions. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem matching_coverage_checked :
    pairBlocks.all (fun a=>pairBlocks.all (fun b=>
      pairBlocks.all (fun c=>matchingCoverageCheck a b c)))=true := by
  decide +kernel

theorem three_blocks_covered (a b c : Nat) (ha : a∈pairBlocks)
    (hb : b∈pairBlocks) (hc : c∈pairBlocks)
    (h : EvenPartition {blockPorts a,blockPorts b,blockPorts c}) :
    partitionCovered {blockPorts a,blockPorts b,blockPorts c}=true := by
  have h1 := List.all_eq_true.mp matching_coverage_checked a ha
  have h2 := List.all_eq_true.mp h1 b hb
  have h3 := List.all_eq_true.mp h2 c hc
  exact of_decide_eq_true h3 h

/-- Every source partition into even blocks is represented by one of the
thirty-one literal block lists, up to its irrelevant block ordering. -/
theorem canonicalCover (B : Finset (Finset (Fin 6))) (h : EvenPartition B) :
    ∃bs∈evenPartitions,B=bs.toFinset.image blockPorts := by
  obtain ⟨hpos,hbound⟩ := h.card_bound
  have hcases : B.card=1 ∨ B.card=2 ∨ B.card=3 := by omega
  rcases hcases with h1 | h2 | h3
  · obtain ⟨b,hb⟩ := Finset.card_eq_one.mp h1
    have hu : b=Finset.univ := by simpa [hb] using h.2.2.2
    refine ⟨[63],by simp [evenPartitions],?_⟩
    simp [hb,hu]
  · obtain ⟨a,b,hab,hB⟩ := Finset.card_eq_two.mp h2
    let am : Fin 64 := ⟨blockMask a,blockMask_lt a⟩
    let bm : Fin 64 := ⟨blockMask b,blockMask_lt b⟩
    have ha : blockPorts am.val=a := blockPorts_blockMask a
    have hb : blockPorts bm.val=b := blockPorts_blockMask b
    have hp : EvenPartition {blockPorts am.val,blockPorts bm.val} := by rw [ha,hb,←hB]; exact h
    have hh := partitionCovered_sound _ (two_blocks_covered am bm hp)
    simpa only [ha,hb,←hB] using hh
  · obtain ⟨a,b,c,hab,hac,hbc,hB⟩ := Finset.card_eq_three.mp h3
    have haB : a∈B := by simp [hB]
    have hbB : b∈B := by simp [hB]
    have hcB : c∈B := by simp [hB]
    have hs : a.card+b.card+c.card=6 := by
      simpa [hB,hab,hac,hbc,add_assoc] using h.sum_card
    have hla := h.block_card_ge_two haB
    have hlb := h.block_card_ge_two hbB
    have hlc := h.block_card_ge_two hcB
    have ha2 : a.card=2 := by omega
    have hb2 : b.card=2 := by omega
    have hc2 : c.card=2 := by omega
    let am : Fin 64 := ⟨blockMask a,blockMask_lt a⟩
    let bm : Fin 64 := ⟨blockMask b,blockMask_lt b⟩
    let cm : Fin 64 := ⟨blockMask c,blockMask_lt c⟩
    have ha : blockPorts am.val=a := blockPorts_blockMask a
    have hb : blockPorts bm.val=b := blockPorts_blockMask b
    have hc : blockPorts cm.val=c := blockPorts_blockMask c
    have ham : am.val∈pairBlocks := pair_mask_mem am (by rw [ha]; exact ha2)
    have hbm : bm.val∈pairBlocks := pair_mask_mem bm (by rw [hb]; exact hb2)
    have hcm : cm.val∈pairBlocks := pair_mask_mem cm (by rw [hc]; exact hc2)
    have hp : EvenPartition {blockPorts am.val,blockPorts bm.val,blockPorts cm.val} := by
      rw [ha,hb,hc,←hB]; exact h
    have hh := partitionCovered_sound _ (three_blocks_covered _ _ _ ham hbm hcm hp)
    simpa only [ha,hb,hc,←hB] using hh

end Paper2.Certificates.DihedralSupport

