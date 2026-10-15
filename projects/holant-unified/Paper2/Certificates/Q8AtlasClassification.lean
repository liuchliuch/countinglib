import Paper2.Certificates.Q8AtlasTree
import Paper2.Certificates.Q8MatchingConstruction

/-! The exact nine compatible leaves split into seven global perfect-matching
families with overlapping edges and two translation atlases, differing by 6↔7. -/
namespace Paper2.Certificates.Q8.Atlas

def globalRows : Fin 7 → Fin 9 := ![0, 3, 4, 5, 6, 7, 8]

def globalAncestor : Fin 7 → Port → Port := ![![1, 0, 3, 2, 5, 4, 7, 6], ![2, 3, 0, 1, 5, 4, 7, 6], ![3, 2, 1, 0, 5, 4, 7, 6], ![4, 5, 3, 2, 0, 1, 7, 6], ![5, 4, 3, 2, 1, 0, 7, 6], ![6, 7, 3, 2, 5, 4, 0, 1], ![7, 6, 3, 2, 5, 4, 1, 0]]

def collisionWitness : Fin 7 → PairIndex × PairIndex × Port × Port := ![(0,1,4,5), (0,1,4,5), (0,1,4,5), (0,1,6,7), (0,1,6,7), (0,1,4,5), (0,1,4,5)]

def SharesEdge (d : PairIndex) (k : Choice) (e : PairIndex) (l : Choice) : Prop :=
  ∃ u v : Port, u ≠ v ∧ fullMate d k u = v ∧ fullMate e l u = v

def CollisionFree (f : Deck) : Prop :=
  ∀ d e, d ≠ e → ¬DisjointDeleted d e → ¬SharesEdge d (f d) e (f e)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_compatible_0 : DeckCompatible (atlasRows 0) := by
  unfold DeckCompatible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_compatible_1 : DeckCompatible (atlasRows 1) := by
  unfold DeckCompatible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_compatible_2 : DeckCompatible (atlasRows 2) := by
  unfold DeckCompatible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_compatible_3 : DeckCompatible (atlasRows 3) := by
  unfold DeckCompatible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_compatible_4 : DeckCompatible (atlasRows 4) := by
  unfold DeckCompatible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_compatible_5 : DeckCompatible (atlasRows 5) := by
  unfold DeckCompatible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_compatible_6 : DeckCompatible (atlasRows 6) := by
  unfold DeckCompatible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_compatible_7 : DeckCompatible (atlasRows 7) := by
  unfold DeckCompatible
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem row_compatible_8 : DeckCompatible (atlasRows 8) := by
  unfold DeckCompatible
  decide +kernel

theorem atlas_rows_compatible (r : Fin 9) : DeckCompatible (atlasRows r) := by
  fin_cases r
  · exact row_compatible_0
  · exact row_compatible_1
  · exact row_compatible_2
  · exact row_compatible_3
  · exact row_compatible_4
  · exact row_compatible_5
  · exact row_compatible_6
  · exact row_compatible_7
  · exact row_compatible_8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem atlas_rows_normalized (r : Fin 9) : atlasRows r 0 = 0 := by
  revert r
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem atlas_rows_injective : Function.Injective atlasRows := by
  decide +kernel

/-- Exactly nine normalized compatible decks, as a genuine finite equivalence. -/
noncomputable def normalizedAtlasEquiv : Fin 9 ≃ {f : Deck // DeckCompatible f ∧ f 0 = 0} :=
  Equiv.ofBijective (fun r => ⟨atlasRows r,atlas_rows_compatible r,atlas_rows_normalized r⟩) (by
    constructor
    · intro r s he
      exact atlas_rows_injective (congrArg Subtype.val he)
    · rintro ⟨f,hf,h0⟩
      obtain ⟨r,hr⟩ := normalized_atlas_cover f hf h0
      exact ⟨r,Subtype.ext hr.symm⟩)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem global_ancestor_valid (i : Fin 7) :
    (∀ v, globalAncestor i (globalAncestor i v) = v) ∧
    (∀ v, globalAncestor i v ≠ v) := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem global_cards_0 (e : PairIndex) :
    fullMate e (atlasRows (globalRows 0) e) = spliceMate (globalAncestor 0) e := by
  revert e
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem global_cards_1 (e : PairIndex) :
    fullMate e (atlasRows (globalRows 1) e) = spliceMate (globalAncestor 1) e := by
  revert e
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem global_cards_2 (e : PairIndex) :
    fullMate e (atlasRows (globalRows 2) e) = spliceMate (globalAncestor 2) e := by
  revert e
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem global_cards_3 (e : PairIndex) :
    fullMate e (atlasRows (globalRows 3) e) = spliceMate (globalAncestor 3) e := by
  revert e
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem global_cards_4 (e : PairIndex) :
    fullMate e (atlasRows (globalRows 4) e) = spliceMate (globalAncestor 4) e := by
  revert e
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem global_cards_5 (e : PairIndex) :
    fullMate e (atlasRows (globalRows 5) e) = spliceMate (globalAncestor 5) e := by
  revert e
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem global_cards_6 (e : PairIndex) :
    fullMate e (atlasRows (globalRows 6) e) = spliceMate (globalAncestor 6) e := by
  revert e
  decide +kernel

theorem global_cards (i : Fin 7) (e : PairIndex) :
    fullMate e (atlasRows (globalRows i) e) = spliceMate (globalAncestor i) e := by
  fin_cases i
  · exact global_cards_0 e
  · exact global_cards_1 e
  · exact global_cards_2 e
  · exact global_cards_3 e
  · exact global_cards_4 e
  · exact global_cards_5 e
  · exact global_cards_6 e

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem collision_witness_valid (i : Fin 7) :
    (collisionWitness i).1 ≠ (collisionWitness i).2.1 ∧
    ¬DisjointDeleted (collisionWitness i).1 (collisionWitness i).2.1 ∧
    (collisionWitness i).2.2.1 ≠ (collisionWitness i).2.2.2 ∧
    fullMate (collisionWitness i).1 (atlasRows (globalRows i) (collisionWitness i).1)
      (collisionWitness i).2.2.1 = (collisionWitness i).2.2.2 ∧
    fullMate (collisionWitness i).2.1 (atlasRows (globalRows i) (collisionWitness i).2.1)
      (collisionWitness i).2.2.1 = (collisionWitness i).2.2.2 := by
  revert i
  decide +kernel

theorem global_row_not_collision_free (i : Fin 7) : ¬CollisionFree (atlasRows (globalRows i)) := by
  intro h
  obtain ⟨hne,hmeet,huv,hleft,hright⟩ := collision_witness_valid i
  exact h _ _ hne hmeet ⟨_,_,huv,hleft,hright⟩

def translationRows : Fin 2 → Fin 9 := ![1,2]

def translationPermutation : Fin 2 → Equiv.Perm Port :=
  ![Equiv.refl Port,Equiv.swap 6 7]

def HasTranslationLabels (f : Deck) : Prop :=
  ∃ p : Equiv.Perm Port, ∀ d v, v ≠ (deleted d).1 → v ≠ (deleted d).2 →
    p (fullMate d (f d) v) = Fin.xor (p v) (Fin.xor (p (deleted d).1) (p (deleted d).2))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem translation_cards (i : Fin 2) (d : PairIndex) (v : Port)
    (h0 : v ≠ (deleted d).1) (h1 : v ≠ (deleted d).2) :
    translationPermutation i (fullMate d (atlasRows (translationRows i) d) v) =
      Fin.xor (translationPermutation i v)
        (Fin.xor (translationPermutation i (deleted d).1) (translationPermutation i (deleted d).2)) := by
  revert i d v
  decide +kernel

theorem translation_row_labels (i : Fin 2) : HasTranslationLabels (atlasRows (translationRows i)) :=
  ⟨translationPermutation i,translation_cards i⟩

/-- Collision-free normalized compatible families have translation form. -/
theorem normalized_collision_free_translation (f : Deck) (hf : DeckCompatible f)
    (h0 : f 0 = 0) (hc : CollisionFree f) : HasTranslationLabels f := by
  obtain ⟨r,rfl⟩ := normalized_atlas_cover f hf h0
  fin_cases r
  · exact False.elim (global_row_not_collision_free 0 hc)
  · exact translation_row_labels 0
  · exact translation_row_labels 1
  · exact False.elim (global_row_not_collision_free 1 hc)
  · exact False.elim (global_row_not_collision_free 2 hc)
  · exact False.elim (global_row_not_collision_free 3 hc)
  · exact False.elim (global_row_not_collision_free 4 hc)
  · exact False.elim (global_row_not_collision_free 5 hc)
  · exact False.elim (global_row_not_collision_free 6 hc)

end Paper2.Certificates.Q8.Atlas
