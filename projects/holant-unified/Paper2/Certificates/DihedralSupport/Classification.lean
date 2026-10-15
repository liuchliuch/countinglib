module
public import Paper2.Certificates.DihedralSupport.ClassificationRows
public import Paper2.Certificates.DihedralSupport.SupportOrbitDisjoint
public import Paper2.Certificates.DihedralSupport.ClassificationFamilyWitness

/-! Exact support-family classification in source Theorem A.1(iii).
The certificate is first proved exhaustive for arbitrary actual supports.
Its survivor set is then checked equal to the literal generated even-block
cosets, the actual signed-permutation orbit, and the empty support. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport

noncomputable def classifiedMasks : Finset Nat := insert 0 (affineMasks ∪ SupportOrbit.orbitMasks)

theorem zero_not_affine : 0 ∉ affineMasks := by
  intro h
  have hh := (affineMasks_positive_bounded 0 h).1
  omega

theorem classification_disjoint :
    0 ∉ affineMasks ∧ 0 ∉ SupportOrbit.orbitMasks ∧
      Disjoint affineMasks SupportOrbit.orbitMasks :=
  ⟨zero_not_affine, SupportOrbit.zero_not_mem, SupportOrbit.orbit_affine_disjoint.symm⟩

theorem classifiedMasks_card : classifiedMasks.card = 873 := by
  have hz : 0 ∉ affineMasks ∪ SupportOrbit.orbitMasks := by
    simp only [Finset.mem_union,not_or]
    exact ⟨zero_not_affine,SupportOrbit.zero_not_mem⟩
  rw [classifiedMasks,Finset.card_insert_of_notMem hz,
    Finset.card_union_of_disjoint SupportOrbit.orbit_affine_disjoint.symm,
    affineMasks_card,SupportOrbit.orbitMasks_card]

theorem survivorMasks_eq_classified : survivorMasks = classifiedMasks := by
  apply Finset.eq_of_subset_of_card_le
  · intro m hm
    obtain ⟨i,hi,he⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
    have hh := survivor_mem_generated ⟨i,List.mem_range.mp hi⟩
    simpa only [classifiedMasks,he] using hh
  · rw [classifiedMasks_card,survivorMasks_card]

theorem admissible_iff_classified (m : Nat) : AdmissibleMask m ↔ m ∈ classifiedMasks := by
  rw [← survivorMasks_eq_classified]
  exact admissible_iff_survivorMasks m

theorem encodeSupport_zero_iff (S : Support6) :
    encodeSupport S = 0 ↔ ∀ x, S x = false := by
  constructor
  · intro h x
    have hx := encodeSupport_spec S x
    rw [h] at hx
    simpa only [Nat.zero_testBit] using hx.symm
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    simp [encodeSupport, testBit_packBits, h]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem maskWordParity_index6 : ∀ x : Fin 6 → Bool,
    maskWordParity (index6 x) = SupportOrbit.parity x := by decide +kernel

theorem admissible_nonempty_one_parity (S : Support6) (h : AdmissibleSupport S)
    (hne : ∃ x, S x = true) :
    ∃ b : Bool, ∀ x, S x = true → SupportOrbit.parity x = b := by
  have hm := (admissible_iff_classified _).mp ((admissibleSupport_iff_mask S).mp h)
  rcases Finset.mem_insert.mp hm with hz | hm
  · have hzS := (encodeSupport_zero_iff S).mp hz
    obtain ⟨x,hx⟩ := hne
    simp [hzS x] at hx
  · rcases Finset.mem_union.mp hm with ha | ho
    · obtain ⟨b,hb⟩ := affineMasks_singleParity _ ha
      refine ⟨b,fun x hx => ?_⟩
      have hh := hb ⟨index6 x,index6_lt x⟩ (by simpa using hx)
      simpa only [maskWordParity_index6] using hh
    · obtain ⟨b,hb⟩ := SupportOrbit.orbit_one_parity ho
      exact ⟨b,fun x hx => hb x (by simpa using hx)⟩

/-- The exact source families, expressed by literal block-indicator spans
and actual Boolean word actions, with their displayed separate counts. -/
theorem source_A_1_iii_generated (S : Support6) :
    (AdmissibleSupport S ↔
      (∀ x,S x=false) ∨
      (∃ bs ∈ evenPartitions,∃ a < 64,encodeSupport S=cosetMask bs a) ∨
      (∃ σ : Equiv.Perm (Fin 6),∃ b : SupportOrbit.Word,
        ∀ x,S x=SupportOrbit.sstar (SupportOrbit.wordAction σ b x))) ∧
    classifiedMasks.card=873 ∧ affineMasks.card=392 ∧
    sixBlockCosets.card=32 ∧ fourTwoCosets.card=240 ∧ matchingCosets.card=120 ∧
    SupportOrbit.orbitMasks.card=480 ∧
    (0∉affineMasks ∧ 0∉SupportOrbit.orbitMasks ∧
      Disjoint affineMasks SupportOrbit.orbitMasks) ∧
    (∀ _h : AdmissibleSupport S,(∃ x,S x=true) →
      ∃ b : Bool,∀ x,S x=true → SupportOrbit.parity x=b) := by
  refine ⟨?_,classifiedMasks_card,affineMasks_card,sixBlockCosets_card,
    fourTwoCosets_card,matchingCosets_card,SupportOrbit.orbitMasks_card,
    classification_disjoint,fun h hn => admissible_nonempty_one_parity S h hn⟩
  rw [admissibleSupport_iff_mask,admissible_iff_classified]
  simp only [classifiedMasks,Finset.mem_insert,Finset.mem_union]
  rw [encodeSupport_zero_iff,affineMasks_generated,SupportOrbit.support_orbit_iff]
  simp only [eq_comm]

end Paper2.Certificates.DihedralSupport

