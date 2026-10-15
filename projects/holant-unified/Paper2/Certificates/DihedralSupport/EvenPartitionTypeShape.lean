module
public import Paper2.Certificates.DihedralSupport.EvenPartitionCoverage
public import Mathlib.Data.Multiset.MapFold

/-! The block-count types of arbitrary even partitions of six ports.
The genuine coverage theorem selects a canonical representative; only the
thirty-one block lists are checked for their count, family and size profile. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport

def blockSizes (B : Finset (Finset (Fin 6))) : Multiset Nat := B.val.map Finset.card

def canonicalTypeShape (bs : List Nat) : Prop :=
  let B := bs.toFinset.image blockPorts
  B.card = bs.length ∧
  (B.card = 1 ↔ bs ∈ [[63]]) ∧
  (B.card = 2 ↔ bs ∈ fourTwoPartitions) ∧
  (B.card = 3 ↔ bs ∈ matchingPartitions) ∧
  (B.card = 1 → blockSizes B = (Multiset.ofList [6])) ∧
  (B.card = 2 → blockSizes B = (Multiset.ofList [4,2])) ∧
  (B.card = 3 → blockSizes B = (Multiset.ofList [2,2,2]))

instance (bs : List Nat) : Decidable (canonicalTypeShape bs) := by
  unfold canonicalTypeShape
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canonical_types_checked :
    evenPartitions.all (fun bs => decide (canonicalTypeShape bs)) = true := by
  decide +kernel

theorem canonical_type_shape (bs : List Nat) (hbs : bs ∈ evenPartitions) :
    canonicalTypeShape bs :=
  of_decide_eq_true (List.all_eq_true.mp canonical_types_checked bs hbs)

theorem canonical_image_card (bs : List Nat) (hbs : bs ∈ evenPartitions) :
    (bs.toFinset.image blockPorts).card = bs.length := (canonical_type_shape bs hbs).1

theorem canonicalCover_card (B : Finset (Finset (Fin 6))) (h : EvenPartition B) :
    ∃ bs ∈ evenPartitions, B = bs.toFinset.image blockPorts ∧ bs.length = B.card := by
  obtain ⟨bs,hbs,hB⟩ := canonicalCover B h
  exact ⟨bs,hbs,hB,by rw [hB,canonical_image_card bs hbs]⟩

theorem canonicalCover_one (B : Finset (Finset (Fin 6))) (h : EvenPartition B)
    (hc : B.card = 1) : ∃ bs ∈ [[63]], B = bs.toFinset.image blockPorts := by
  obtain ⟨bs,hbs,hB⟩ := canonicalCover B h
  refine ⟨bs,(canonical_type_shape bs hbs).2.1.mp ?_,hB⟩
  simpa only [← hB] using hc

theorem canonicalCover_two (B : Finset (Finset (Fin 6))) (h : EvenPartition B)
    (hc : B.card = 2) : ∃ bs ∈ fourTwoPartitions, B = bs.toFinset.image blockPorts := by
  obtain ⟨bs,hbs,hB⟩ := canonicalCover B h
  refine ⟨bs,(canonical_type_shape bs hbs).2.2.1.mp ?_,hB⟩
  simpa only [← hB] using hc

theorem canonicalCover_three (B : Finset (Finset (Fin 6))) (h : EvenPartition B)
    (hc : B.card = 3) : ∃ bs ∈ matchingPartitions, B = bs.toFinset.image blockPorts := by
  obtain ⟨bs,hbs,hB⟩ := canonicalCover B h
  refine ⟨bs,(canonical_type_shape bs hbs).2.2.2.1.mp ?_,hB⟩
  simpa only [← hB] using hc

theorem EvenPartition.blockSizes_one {B : Finset (Finset (Fin 6))} (h : EvenPartition B)
    (hc : B.card = 1) : blockSizes B = Multiset.ofList [6] := by
  obtain ⟨bs,hbs,hB⟩ := canonicalCover B h
  rw [hB]
  exact (canonical_type_shape bs hbs).2.2.2.2.1 (by simpa only [← hB] using hc)

theorem EvenPartition.blockSizes_two {B : Finset (Finset (Fin 6))} (h : EvenPartition B)
    (hc : B.card = 2) : blockSizes B = Multiset.ofList [4,2] := by
  obtain ⟨bs,hbs,hB⟩ := canonicalCover B h
  rw [hB]
  exact (canonical_type_shape bs hbs).2.2.2.2.2.1 (by simpa only [← hB] using hc)

theorem EvenPartition.blockSizes_three {B : Finset (Finset (Fin 6))} (h : EvenPartition B)
    (hc : B.card = 3) : blockSizes B = Multiset.ofList [2,2,2] := by
  obtain ⟨bs,hbs,hB⟩ := canonicalCover B h
  rw [hB]
  exact (canonical_type_shape bs hbs).2.2.2.2.2.2 (by simpa only [← hB] using hc)

theorem evenPartitions_of_six (bs : List Nat) (hbs : bs ∈ [[63]]) : bs ∈ evenPartitions := by
  simp only [List.mem_singleton] at hbs
  subst bs
  simp [evenPartitions]

theorem evenPartitions_of_fourTwo (bs : List Nat) (hbs : bs ∈ fourTwoPartitions) :
    bs ∈ evenPartitions := by simp [evenPartitions,hbs]

theorem evenPartitions_of_matching (bs : List Nat) (hbs : bs ∈ matchingPartitions) :
    bs ∈ evenPartitions := by simp [evenPartitions,hbs]

theorem canonical_one_card (bs : List Nat) (hbs : bs ∈ [[63]]) :
    (bs.toFinset.image blockPorts).card = 1 :=
  (canonical_type_shape bs (evenPartitions_of_six bs hbs)).2.1.mpr hbs

theorem canonical_two_card (bs : List Nat) (hbs : bs ∈ fourTwoPartitions) :
    (bs.toFinset.image blockPorts).card = 2 :=
  (canonical_type_shape bs (evenPartitions_of_fourTwo bs hbs)).2.2.1.mpr hbs

theorem canonical_three_card (bs : List Nat) (hbs : bs ∈ matchingPartitions) :
    (bs.toFinset.image blockPorts).card = 3 :=
  (canonical_type_shape bs (evenPartitions_of_matching bs hbs)).2.2.2.1.mpr hbs

theorem canonicalCover_one_iff (B : Finset (Finset (Fin 6))) (h : EvenPartition B) :
    B.card = 1 ↔ ∃ bs ∈ [[63]], B = bs.toFinset.image blockPorts := by
  constructor
  · exact canonicalCover_one B h
  · rintro ⟨bs,hbs,rfl⟩
    exact canonical_one_card bs hbs

theorem canonicalCover_two_iff (B : Finset (Finset (Fin 6))) (h : EvenPartition B) :
    B.card = 2 ↔ ∃ bs ∈ fourTwoPartitions, B = bs.toFinset.image blockPorts := by
  constructor
  · exact canonicalCover_two B h
  · rintro ⟨bs,hbs,rfl⟩
    exact canonical_two_card bs hbs

theorem canonicalCover_three_iff (B : Finset (Finset (Fin 6))) (h : EvenPartition B) :
    B.card = 3 ↔ ∃ bs ∈ matchingPartitions, B = bs.toFinset.image blockPorts := by
  constructor
  · exact canonicalCover_three B h
  · rintro ⟨bs,hbs,rfl⟩
    exact canonical_three_card bs hbs

end Paper2.Certificates.DihedralSupport
