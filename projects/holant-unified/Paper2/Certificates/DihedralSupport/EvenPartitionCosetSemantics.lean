module
public import Paper2.Certificates.DihedralSupport.EvenPartitionCosets
public import Paper2.Certificates.DihedralSupport.EvenPartitionCoverage
public import Paper2.Certificates.DihedralSupport.ClassificationSemantics
public import Mathlib.Data.Finset.Powerset

/-! The affine masks are exactly the literal cosets of arbitrary unordered
even partitions. A span word is the indicator of the union of any selected
subset of blocks. The only finite checks concern the thirty-one partitions,
not a list of surviving support masks. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport
set_option maxHeartbeats 2000000

def partitionSpanWords (B : Finset (Finset (Fin 6))) : Finset (Fin 6 → Bool) :=
  B.powerset.image (fun C => fun k => decide (k ∈ C.biUnion id))

def wordXor (a b : Fin 6 → Bool) : Fin 6 → Bool := fun k => a k ^^ b k

def translatedSupport (a : Fin 6 → Bool) (W : Finset (Fin 6 → Bool)) : Support6 :=
  fun x => decide (x ∈ W.image (wordXor a))

/-- A translate of the actual subset-union span of an arbitrary source
partition into nonempty, pairwise disjoint even blocks covering all ports. -/
def EvenPartitionCoset (S : Support6) : Prop :=
  ∃ B : Finset (Finset (Fin 6)), EvenPartition B ∧
    ∃ a : Fin 6 → Bool, S = translatedSupport a (partitionSpanWords B)

@[simp] theorem mem_partitionSpanWords (B : Finset (Finset (Fin 6))) (x : Fin 6 → Bool) :
    x ∈ partitionSpanWords B ↔
      ∃ C ⊆ B, x = (fun k => decide (k ∈ C.biUnion id)) := by
  simp only [partitionSpanWords,Finset.mem_image,Finset.mem_powerset]
  constructor
  · rintro ⟨C,hC,hx⟩
    exact ⟨C,hC,hx.symm⟩
  · rintro ⟨C,hC,hx⟩
    exact ⟨C,hC,hx.symm⟩

@[simp] theorem word6_xor (a b : Nat) :
    word6 (a ^^^ b) = wordXor (word6 a) (word6 b) := by
  funext k
  simp [word6,wordXor,Nat.testBit_xor]

theorem testBit_maskOfWords (words : List Nat) (i : Nat) :
    (maskOfWords words).testBit i = decide (i ∈ words) := by
  induction words with
  | nil => simp [maskOfWords]
  | cons w ws ih =>
    change ((2^w) ||| maskOfWords ws).testBit i = decide (i ∈ w :: ws)
    rw [Nat.testBit_or,ih]
    by_cases hi : w = i
    · subst w
      simp
    · simp [hi,Ne.symm hi]

theorem xor_lt_64 {a b : Nat} (ha : a < 64) (hb : b < 64) : a ^^^ b < 64 := by
  change a ^^^ b < 2^6
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hp : 2^6 ≤ 2^i := Nat.pow_le_pow_right (by decide) hi
  have ha' : a < 2^i := lt_of_lt_of_le ha hp
  have hb' : b < 2^i := lt_of_lt_of_le hb hp
  simp [Nat.testBit_xor,Nat.testBit_eq_false_of_lt ha',Nat.testBit_eq_false_of_lt hb']

theorem maskOfWords_lt (words : List Nat) (h : ∀ w ∈ words,w < 64) :
    maskOfWords words < 18446744073709551616 := by
  change maskOfWords words < 2^64
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  have hn : i ∉ words := by intro hm; have := h i hm; omega
  simp [testBit_maskOfWords,hn]

theorem mem_word6_list (words : List Nat) (h : ∀ w ∈ words,w < 64)
    (i : Nat) (hi : i < 64) :
    word6 i ∈ (words.map word6).toFinset ↔ i ∈ words := by
  simp only [List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨w,hw,he⟩
    have hh := congrArg index6 he
    have hw' := index6_word6 ⟨w,h w hw⟩
    have hi' := index6_word6 ⟨i,hi⟩
    have hwi : w = i := hw'.symm.trans (hh.trans hi')
    exact hwi ▸ hw
  · intro hm
    exact ⟨i,hm,rfl⟩

theorem encode_word_list (words : List Nat) (h : ∀ w ∈ words,w < 64) :
    encodeSupport (fun x => decide (x ∈ (words.map word6).toFinset)) = maskOfWords words := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simp only [encodeSupport,testBit_packBits,hi,decide_true,Bool.true_and,testBit_maskOfWords]
    simp only [mem_word6_list words h i hi]
  · have hn : i ∉ words := by intro hm; have := h i hm; omega
    simp [encodeSupport,testBit_packBits,hi,testBit_maskOfWords,hn]

/- These checks contain 31 block lists, each with at most three blocks and
eight subset sums. They inspect the actual subset-union span definition. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canonical_span_checked :
    evenPartitions.all (fun bs => decide
      (partitionSpanWords (bs.toFinset.image blockPorts) = ((blockSpan bs).map word6).toFinset)) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canonical_partitions_even_checked :
    evenPartitions.all (fun bs => decide (EvenPartition (bs.toFinset.image blockPorts))) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem canonical_spans_bounded_checked :
    evenPartitions.all (fun bs => (blockSpan bs).all (fun w => decide (w < 64))) = true := by
  decide +kernel

theorem canonical_span (bs : List Nat) (hbs : bs ∈ evenPartitions) :
    partitionSpanWords (bs.toFinset.image blockPorts) = ((blockSpan bs).map word6).toFinset :=
  of_decide_eq_true (List.all_eq_true.mp canonical_span_checked bs hbs)

theorem canonical_partition_even (bs : List Nat) (hbs : bs ∈ evenPartitions) :
    EvenPartition (bs.toFinset.image blockPorts) :=
  of_decide_eq_true (List.all_eq_true.mp canonical_partitions_even_checked bs hbs)

theorem canonical_span_bound (bs : List Nat) (hbs : bs ∈ evenPartitions)
    (w : Nat) (hw : w ∈ blockSpan bs) : w < 64 :=
  of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp canonical_spans_bounded_checked bs hbs) w hw)

theorem translate_word_list (words : List Nat) (a : Nat) :
    ((words.map word6).toFinset).image (wordXor (word6 a)) =
      ((words.map (fun w => word6 (a ^^^ w))).toFinset) := by
  ext x
  simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
  constructor
  · rintro ⟨y,⟨w,hw,rfl⟩,rfl⟩
    exact ⟨w,hw,word6_xor a w⟩
  · rintro ⟨w,hw,hx⟩
    refine ⟨word6 w,⟨w,hw,rfl⟩,?_⟩
    rw [←word6_xor]
    exact hx

/-- The executable coset mask encodes exactly the literal translated
subset-union span of the actual canonical partition. -/
theorem encode_canonical_coset (bs : List Nat) (hbs : bs ∈ evenPartitions)
    (a : Nat) (ha : a < 64) :
    encodeSupport (translatedSupport (word6 a)
      (partitionSpanWords (bs.toFinset.image blockPorts))) = cosetMask bs a := by
  rw [canonical_span bs hbs]
  unfold translatedSupport
  rw [translate_word_list]
  have hbound : ∀ w ∈ (blockSpan bs).map (fun w => a ^^^ w),w < 64 := by
    intro w hw
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hw
    exact xor_lt_64 ha (canonical_span_bound bs hbs v hv)
  simpa only [List.map_map,Function.comp_def,cosetMask] using
    encode_word_list ((blockSpan bs).map (fun w => a ^^^ w)) hbound

/-- Appendix A.1(iii): membership in the computed affine masks is
equivalent to the source's arbitrary even-partition coset geometry. -/
theorem evenPartitionCoset_iff_affineMasks (S : Support6) :
    EvenPartitionCoset S ↔ encodeSupport S ∈ affineMasks := by
  constructor
  · rintro ⟨B,hB,a,rfl⟩
    obtain ⟨bs,hbs,rfl⟩ := canonicalCover B hB
    apply (affineMasks_generated _).mpr
    refine ⟨bs,hbs,index6 a,index6_lt a,?_⟩
    rw [←encode_canonical_coset bs hbs (index6 a) (index6_lt a),word6_index6]
  · intro hm
    obtain ⟨bs,hbs,a,ha,he⟩ := (affineMasks_generated _).mp hm
    refine ⟨bs.toFinset.image blockPorts,canonical_partition_even bs hbs,word6 a,?_⟩
    apply encodeSupport_injective
    rw [encode_canonical_coset bs hbs a ha]
    exact he.symm

end Paper2.Certificates.DihedralSupport

