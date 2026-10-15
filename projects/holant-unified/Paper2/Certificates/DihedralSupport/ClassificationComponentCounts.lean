module
public import Paper2.Certificates.DihedralSupport.ClassificationCardinality

/-! Counts of actual Boolean supports in each of the three literal even
partition types. Support encoding is a proved bijection, so the counts do
not merely count selected translated block presentations with duplicates. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport

theorem cosetsOf_mono {P Q : List (List Nat)} (h : ∀ bs ∈ P,bs ∈ Q) :
    cosetsOf P ⊆ cosetsOf Q := by
  intro m hm
  obtain ⟨bs,hbs,hh⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hm)
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hh
  exact List.mem_toFinset.mpr
    (List.mem_flatMap.mpr ⟨bs,h bs hbs,List.mem_map.mpr ⟨a,ha,he⟩⟩)

theorem sixBlockCosets_subset_affine : sixBlockCosets ⊆ affineMasks := by
  apply cosetsOf_mono
  intro bs hb
  exact List.mem_append_left _ (List.mem_append_left _ hb)

theorem fourTwoCosets_subset_affine : fourTwoCosets ⊆ affineMasks := by
  apply cosetsOf_mono
  intro bs hb
  exact List.mem_append_left _ (List.mem_append_right _ hb)

theorem matchingCosets_subset_affine : matchingCosets ⊆ affineMasks := by
  apply cosetsOf_mono
  intro bs hb
  exact List.mem_append_right _ hb

theorem sixBlock_support_count :
    Nat.card {S : Support6 // encodeSupport S ∈ sixBlockCosets} = 32 :=
  (support_family_card _ (fun m hm =>
    (affineMasks_positive_bounded m (sixBlockCosets_subset_affine hm)).2)).trans sixBlockCosets_card

theorem fourTwo_support_count :
    Nat.card {S : Support6 // encodeSupport S ∈ fourTwoCosets} = 240 :=
  (support_family_card _ (fun m hm =>
    (affineMasks_positive_bounded m (fourTwoCosets_subset_affine hm)).2)).trans fourTwoCosets_card

theorem matching_support_count :
    Nat.card {S : Support6 // encodeSupport S ∈ matchingCosets} = 120 :=
  (support_family_card _ (fun m hm =>
    (affineMasks_positive_bounded m (matchingCosets_subset_affine hm)).2)).trans matchingCosets_card

end Paper2.Certificates.DihedralSupport
