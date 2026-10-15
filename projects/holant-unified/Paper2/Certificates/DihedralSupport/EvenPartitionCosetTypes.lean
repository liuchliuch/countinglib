module
public import Paper2.Certificates.DihedralSupport.EvenPartitionTypeShape
public import Paper2.Certificates.DihedralSupport.EvenPartitionLinearCosets
public import Paper2.Certificates.DihedralSupport.ClassificationComponentCounts

/-! Source block types for actual supports. A type is witnessed by an
arbitrary original even partition with the indicated number of blocks,
and by the literal translate of its actual F₂ block-indicator span.
The component counts therefore count distinct supports, not presentations. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport

/-- Typed subset-union version of the source affine coset. -/
def EvenPartitionCosetOfCard (k : Nat) (S : Support6) : Prop :=
  ∃ B : Finset (Finset (Fin 6)), EvenPartition B ∧ B.card = k ∧
    ∃ a : Fin 6 → Bool, S = translatedSupport a (partitionSpanWords B)

/-- Typed literal translate of the actual F₂ linear span of the original
partition block indicators. The partition and translation are unrestricted. -/
def EvenPartitionLinearCosetOfCard (k : Nat) (S : Support6) : Prop :=
  ∃ B : Finset (Finset (Fin 6)), EvenPartition B ∧ B.card = k ∧
    ∃ a : Fin 6 → Bool, ∀ x : Fin 6 → Bool,
      S x = true ↔ ∃ v : Fin 6 → ZMod 2,
        v ∈ blockLinearSpan B ∧ wordVector x = wordVector a + v

theorem linearCosetOfCard_iff (k : Nat) (S : Support6) :
    EvenPartitionLinearCosetOfCard k S ↔ EvenPartitionCosetOfCard k S := by
  classical
  constructor
  · rintro ⟨B,hB,hk,a,hS⟩
    refine ⟨B,hB,hk,a,?_⟩
    funext x
    apply Bool.eq_iff_iff.mpr
    exact (hS x).trans (translatedSupport_linearSpan B hB a x).symm
  · rintro ⟨B,hB,hk,a,rfl⟩
    exact ⟨B,hB,hk,a,translatedSupport_linearSpan B hB a⟩

theorem cosetOfCard_iff_canonical (k : Nat) (S : Support6) :
    EvenPartitionCosetOfCard k S ↔
      ∃ bs ∈ evenPartitions, (bs.toFinset.image blockPorts).card = k ∧
        ∃ a < 64, encodeSupport S = cosetMask bs a := by
  constructor
  · rintro ⟨B,hB,hk,a,rfl⟩
    obtain ⟨bs,hbs,hcanon⟩ := canonicalCover B hB
    refine ⟨bs,hbs,by simpa only [←hcanon] using hk,index6 a,index6_lt a,?_⟩
    rw [hcanon]
    simpa only [word6_index6] using encode_canonical_coset bs hbs (index6 a) (index6_lt a)
  · rintro ⟨bs,hbs,hk,a,ha,he⟩
    refine ⟨bs.toFinset.image blockPorts,canonical_partition_even bs hbs,hk,word6 a,?_⟩
    apply encodeSupport_injective
    rw [encode_canonical_coset bs hbs a ha]
    exact he

theorem cosetsOf_generated (P : List (List Nat)) (m : Nat) :
    m ∈ cosetsOf P ↔ ∃ bs ∈ P, ∃ a < 64, cosetMask bs a = m := by
  simp only [cosetsOf,List.mem_toFinset,List.mem_flatMap,List.mem_map,List.mem_range]

private theorem cosetOfCard_family_iff (P : List (List Nat)) (k : Nat)
    (hP : ∀ bs ∈ P, bs ∈ evenPartitions)
    (ht : ∀ bs ∈ evenPartitions, (bs.toFinset.image blockPorts).card = k ↔ bs ∈ P)
    (S : Support6) : EvenPartitionCosetOfCard k S ↔ encodeSupport S ∈ cosetsOf P := by
  rw [cosetOfCard_iff_canonical,cosetsOf_generated]
  constructor
  · rintro ⟨bs,hbs,hk,a,ha,he⟩
    exact ⟨bs,(ht bs hbs).mp hk,a,ha,he.symm⟩
  · rintro ⟨bs,hbs,a,ha,he⟩
    have hc := hP bs hbs
    exact ⟨bs,hc,(ht bs hc).mpr hbs,a,ha,he.symm⟩

theorem cosetOfCard_iff_sixBlock (S : Support6) :
    EvenPartitionCosetOfCard 1 S ↔ encodeSupport S ∈ sixBlockCosets :=
  cosetOfCard_family_iff [[63]] 1 evenPartitions_of_six
    (fun bs hbs => (canonical_type_shape bs hbs).2.1) S

theorem cosetOfCard_iff_fourTwo (S : Support6) :
    EvenPartitionCosetOfCard 2 S ↔ encodeSupport S ∈ fourTwoCosets :=
  cosetOfCard_family_iff fourTwoPartitions 2 evenPartitions_of_fourTwo
    (fun bs hbs => (canonical_type_shape bs hbs).2.2.1) S

theorem cosetOfCard_iff_matching (S : Support6) :
    EvenPartitionCosetOfCard 3 S ↔ encodeSupport S ∈ matchingCosets :=
  cosetOfCard_family_iff matchingPartitions 3 evenPartitions_of_matching
    (fun bs hbs => (canonical_type_shape bs hbs).2.2.2.1) S

theorem linearCosetOfCard_iff_sixBlock (S : Support6) :
    EvenPartitionLinearCosetOfCard 1 S ↔ encodeSupport S ∈ sixBlockCosets :=
  (linearCosetOfCard_iff 1 S).trans (cosetOfCard_iff_sixBlock S)

theorem linearCosetOfCard_iff_fourTwo (S : Support6) :
    EvenPartitionLinearCosetOfCard 2 S ↔ encodeSupport S ∈ fourTwoCosets :=
  (linearCosetOfCard_iff 2 S).trans (cosetOfCard_iff_fourTwo S)

theorem linearCosetOfCard_iff_matching (S : Support6) :
    EvenPartitionLinearCosetOfCard 3 S ↔ encodeSupport S ∈ matchingCosets :=
  (linearCosetOfCard_iff 3 S).trans (cosetOfCard_iff_matching S)

theorem sixBlock_linearCoset_count :
    Nat.card {S : Support6 // EvenPartitionLinearCosetOfCard 1 S} = 32 := by
  let e := Equiv.subtypeEquivRight linearCosetOfCard_iff_sixBlock
  exact (Nat.card_congr e).trans sixBlock_support_count

theorem fourTwo_linearCoset_count :
    Nat.card {S : Support6 // EvenPartitionLinearCosetOfCard 2 S} = 240 := by
  let e := Equiv.subtypeEquivRight linearCosetOfCard_iff_fourTwo
  exact (Nat.card_congr e).trans fourTwo_support_count

theorem matching_linearCoset_count :
    Nat.card {S : Support6 // EvenPartitionLinearCosetOfCard 3 S} = 120 := by
  let e := Equiv.subtypeEquivRight linearCosetOfCard_iff_matching
  exact (Nat.card_congr e).trans matching_support_count

theorem evenPartitionLinearCoset_iff_types (S : Support6) :
    EvenPartitionLinearCoset S ↔
      EvenPartitionLinearCosetOfCard 1 S ∨ EvenPartitionLinearCosetOfCard 2 S ∨
        EvenPartitionLinearCosetOfCard 3 S := by
  constructor
  · rintro ⟨B,hB,a,hS⟩
    have hb := hB.card_bound
    have hc : B.card = 1 ∨ B.card = 2 ∨ B.card = 3 := by omega
    rcases hc with h1 | h2 | h3
    · exact Or.inl ⟨B,hB,h1,a,hS⟩
    · exact Or.inr (Or.inl ⟨B,hB,h2,a,hS⟩)
    · exact Or.inr (Or.inr ⟨B,hB,h3,a,hS⟩)
  · rintro (⟨B,hB,_,a,hS⟩ | ⟨B,hB,_,a,hS⟩ | ⟨B,hB,_,a,hS⟩) <;>
      exact ⟨B,hB,a,hS⟩

/-- The typed source witnesses carry the stated actual block-size profile. -/
theorem linearCosetOfCard_one_shape (S : Support6)
    (h : EvenPartitionLinearCosetOfCard 1 S) :
    ∃ B : Finset (Finset (Fin 6)), EvenPartition B ∧
      blockSizes B = Multiset.ofList [6] ∧
      ∃ a : Fin 6 → Bool, ∀ x : Fin 6 → Bool,
        S x = true ↔ ∃ v : Fin 6 → ZMod 2,
          v ∈ blockLinearSpan B ∧ wordVector x = wordVector a + v := by
  obtain ⟨B,hB,hk,a,hS⟩ := h
  exact ⟨B,hB,hB.blockSizes_one hk,a,hS⟩

theorem linearCosetOfCard_two_shape (S : Support6)
    (h : EvenPartitionLinearCosetOfCard 2 S) :
    ∃ B : Finset (Finset (Fin 6)), EvenPartition B ∧
      blockSizes B = Multiset.ofList [4,2] ∧
      ∃ a : Fin 6 → Bool, ∀ x : Fin 6 → Bool,
        S x = true ↔ ∃ v : Fin 6 → ZMod 2,
          v ∈ blockLinearSpan B ∧ wordVector x = wordVector a + v := by
  obtain ⟨B,hB,hk,a,hS⟩ := h
  exact ⟨B,hB,hB.blockSizes_two hk,a,hS⟩

theorem linearCosetOfCard_three_shape (S : Support6)
    (h : EvenPartitionLinearCosetOfCard 3 S) :
    ∃ B : Finset (Finset (Fin 6)), EvenPartition B ∧
      blockSizes B = Multiset.ofList [2,2,2] ∧
      ∃ a : Fin 6 → Bool, ∀ x : Fin 6 → Bool,
        S x = true ↔ ∃ v : Fin 6 → ZMod 2,
          v ∈ blockLinearSpan B ∧ wordVector x = wordVector a + v := by
  obtain ⟨B,hB,hk,a,hS⟩ := h
  exact ⟨B,hB,hB.blockSizes_three hk,a,hS⟩

end Paper2.Certificates.DihedralSupport
