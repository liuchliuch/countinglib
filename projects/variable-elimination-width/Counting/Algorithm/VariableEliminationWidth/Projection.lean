import Counting.Algorithm.VariableEliminationWidth.Bags

/-! # Projection and deletion of supplied bag-tree leaves -/

namespace Counting.Algorithm.VariableEliminationWidth

open Counting.Algorithm.VariableElimination

variable {V : Type} [DecidableEq V]

/-- Removing a vertex preserves the actual parent indices and leaf attachments. -/
def BagTree.project (v : V) : {bags : List (Finset V)} → BagTree bags →
    BagTree (bags.map (projectBag v))
  | _, .root bag => .root (projectBag v bag)
  | _, @BagTree.attach _ _ bag bags rest parent overlap =>
      .attach (projectBag v bag) (rest.project v)
        ⟨parent.val, by simpa only [List.length_map] using parent.isLt⟩ (by
          intro other ho w hw
          obtain ⟨old, hold, rfl⟩ := List.mem_map.mp ho
          have hl : w.val ∈ bag := (mem_projectBag v bag w).mp (Finset.mem_inter.mp hw).1
          have hr : w.val ∈ old := (mem_projectBag v old w).mp (Finset.mem_inter.mp hw).2
          have hp := overlap old hold (Finset.mem_inter.mpr ⟨hl, hr⟩)
          simpa only [List.get_eq_getElem, List.getElem_map, mem_projectBag] using hp)

/-- All vertex coverage and input bag-size bounds survive an actual projection. -/
def Decomposition.project {width : Nat} (d : Decomposition V width) (v : V) :
    Decomposition (Remaining v) width where
  bags := d.bags.map (projectBag v)
  tree := d.tree.project v
  cover := by
    intro w
    obtain ⟨bag, hb, hw⟩ := d.cover w.val
    exact ⟨projectBag v bag, List.mem_map.mpr ⟨bag, hb, rfl⟩, (mem_projectBag v bag w).mpr hw⟩
  card_le := by
    intro bag hb
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hb
    exact (card_projectBag_le v old).trans (d.card_le old hold)

/-- Remove a leaf which is already contained in its parent. The returned bag-tree
is the actual previous subtree, with unchanged bags and parent indices. -/
def dropLeaf {width : Nat} (bag : Finset V) (bags : List (Finset V))
    (rest : BagTree bags) (parent : Fin bags.length)
    (overlap : ∀ other ∈ bags, bag ∩ other ⊆ bags.get parent)
    (cover : ∀ v : V, ∃ b ∈ bag :: bags, v ∈ b)
    (bound : ∀ b ∈ bag :: bags, b.card ≤ width + 1)
    (empty : privateVertices bag bags = ∅) : Decomposition V width where
  bags := bags
  tree := rest
  cover := by
    intro v
    obtain ⟨b, hb, hv⟩ := cover v
    rcases List.mem_cons.mp hb with heq | hb
    · subst b
      exact ⟨bags.get parent, List.get_mem _ _, leaf_subset_parent bag bags parent overlap empty hv⟩
    · exact ⟨b, hb, hv⟩
  card_le := fun b hb => bound b (List.mem_cons_of_mem _ hb)

/-- Deleting an absorbed leaf keeps every factor in some surviving bag. -/
theorem bagged_dropLeaf {D R : Type} (bag : Finset V) (bags : List (Finset V))
    (parent : Fin bags.length)
    (overlap : ∀ other ∈ bags, bag ∩ other ⊆ bags.get parent)
    (empty : privateVertices bag bags = ∅)
    (fs : List (Factor V D R)) (covered : Bagged (bag :: bags) fs) : Bagged bags fs := by
  intro f hf
  obtain ⟨b, hb, hs⟩ := covered f hf
  rcases List.mem_cons.mp hb with heq | hb
  · subst b
    exact ⟨bags.get parent, List.get_mem _ _, hs.trans (leaf_subset_parent bag bags parent overlap empty)⟩
  · exact ⟨b, hb, hs⟩

end Counting.Algorithm.VariableEliminationWidth
