import Counting.Algorithm.VariableEliminationTreewidth.Leaf

/-! # Node-preserving parent-attachment listings -/

namespace Counting.Algorithm.VariableEliminationTreewidth
open Counting.Algorithm.VariableEliminationWidth

variable {V I : Type} [DecidableEq V]

/-- The conversion output lists the original tree nodes exactly once and carries
the frozen D3 bag-tree structure on their unchanged bags. -/
structure BagListing (bag : I → Finset V) where
  nodes : List I
  nodup : nodes.Nodup
  complete : ∀ i : I, i ∈ nodes
  tree : BagTree (nodes.map bag)

variable [DecidableEq I]

/-- Locate a real node in the constructed listing by executable finite search. -/
def BagListing.index {bag : I → Finset V} (listing : BagListing bag) (i : I) :
    Fin listing.nodes.length := ⟨listing.nodes.idxOf i, List.idxOf_lt_length_of_mem (listing.complete i)⟩

@[simp] theorem BagListing.get_index {bag : I → Finset V} (listing : BagListing bag) (i : I) :
    listing.nodes.get (listing.index i) = i := by
  simp [BagListing.index, List.get_eq_getElem]

/-- A singleton graph produces one real input bag. -/
def BagListing.singleton [Subsingleton I] (bag : I → Finset V) (root : I) : BagListing bag where
  nodes := [root]
  nodup := by simp
  complete := by intro i; simp [Subsingleton.elim i root]
  tree := .root (bag root)

/-- Attach the deleted graph leaf to its actual neighbour in the recursive
node listing. No input bag or node is duplicated or synthesized. -/
def BagListing.attach (bag : I → Finset V) (leaf : I)
    (rest : BagListing (fun i : {i : I // i ≠ leaf} => bag i.val))
    (parent : {i : I // i ≠ leaf})
    (separator : ∀ i : {i : I // i ≠ leaf}, bag leaf ∩ bag i.val ⊆ bag parent.val) :
    BagListing bag where
  nodes := leaf :: rest.nodes.map Subtype.val
  nodup := by
    rw [List.nodup_cons]
    constructor
    · intro h
      obtain ⟨i, hi, heq⟩ := List.mem_map.mp h
      exact i.property heq
    · exact rest.nodup.map Subtype.val_injective
  complete := by
    intro i
    by_cases h : i = leaf
    · simp [h]
    · exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨⟨i, h⟩, rest.complete _, rfl⟩)
  tree := by
    let parentIndex : Fin (rest.nodes.map (fun i => bag i.val)).length :=
      ⟨(rest.index parent).val, by simpa only [List.length_map] using (rest.index parent).isLt⟩
    have hget : (rest.nodes.map (fun i => bag i.val)).get parentIndex = bag parent.val := by
      simp only [List.get_eq_getElem, List.getElem_map, parentIndex]
      exact congrArg (fun i => bag i.val) (rest.get_index parent)
    have tree : BagTree (bag leaf :: rest.nodes.map (fun i => bag i.val)) :=
      .attach (bag leaf) rest.tree parentIndex (by
        intro other ho
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
        rw [hget]
        exact separator i)
    change BagTree (bag leaf :: (rest.nodes.map Subtype.val).map bag)
    rw [List.map_map]
    exact tree

end Counting.Algorithm.VariableEliminationTreewidth
