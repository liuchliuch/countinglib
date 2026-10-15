import Counting.Algorithm.VariableEliminationWidth.Bags
import Counting.Algorithm.VariableElimination.Program

/-! # Leaf-private elimination and the induced bucket invariant -/

namespace Counting.Algorithm.VariableEliminationWidth

open Counting.Algorithm.VariableElimination

variable {V D R : Type} [Fintype V] [LinearOrder V]

omit [Fintype V] in
/-- No incident occurrence can be covered by a different bag when its pivot is
private to this leaf. This is derived from factor coverage and private membership. -/
theorem incident_subset_leaf (bag : Finset V) (rest : List (Finset V))
    (fs : List (Factor V D R)) (covered : Bagged (bag :: rest) fs)
    (v : V) (hprivate : v ∈ privateVertices bag rest)
    (f : Factor V D R) (hf : f ∈ bucket v fs) : f.support ⊆ bag := by
  have hfs := List.mem_filter.mp hf
  obtain ⟨other, ho, hsub⟩ := covered f hfs.1
  rcases List.mem_cons.mp ho with rfl | ho
  · exact hsub
  · have hvf : v ∈ f.support := by simpa using hfs.2
    have hvo := hsub hvf
    exact False.elim (((mem_privateVertices v bag rest).mp hprivate).2 other ho hvo)

/-- The executor's dynamically computed scope is contained in the input leaf
bag with the pivot removed. It is not supplied as a decomposition hypothesis. -/
theorem bucketVars_subset_leaf (bag : Finset V) (rest : List (Finset V))
    (fs : List (Factor V D R)) (covered : Bagged (bag :: rest) fs)
    (v : V) (hprivate : v ∈ privateVertices bag rest) :
    (bucketVars v fs).toFinset ⊆ projectBag v bag := by
  intro w hw
  have hws := (mem_bucketVars v fs w).mp (List.mem_toFinset.mp hw)
  obtain ⟨f, hf, hwf⟩ := (mem_support _ _).mp hws
  exact (mem_projectBag v bag w).mpr
    (incident_subset_leaf bag rest fs covered v hprivate f hf hwf)

/-- An input bag bound yields the actual induced bucket-scope bound. Port arities
may be larger because repeated ports are retained by the real factors. -/
theorem bucketVars_length_le (bag : Finset V) (rest : List (Finset V))
    (fs : List (Factor V D R)) (covered : Bagged (bag :: rest) fs)
    (v : V) (hprivate : v ∈ privateVertices bag rest) (width : Nat)
    (hwidth : bag.card ≤ width + 1) : (bucketVars v fs).length ≤ width := by
  have hv : v ∈ bag := ((mem_privateVertices v bag rest).mp hprivate).1
  calc
    (bucketVars v fs).length = (bucketVars v fs).toFinset.card := by simp [bucketVars]
    _ ≤ (projectBag v bag).card :=
      Finset.card_le_card (bucketVars_subset_leaf bag rest fs covered v hprivate)
    _ = bag.card - 1 := by rw [card_projectBag, Finset.card_erase_of_mem hv]
    _ ≤ width := by omega

omit [Fintype V] in
/-- Projecting a retained occurrence changes only the variable type; its distinct
support fits in the projected copy of any bag that contained it before. -/
theorem support_retain_subset (v : V) (f : Factor V D R) (h : v ∉ f.support)
    (bag : Finset V) (hbag : f.support ⊆ bag) :
    (retain v f h).support ⊆ projectBag v bag := by
  intro w hw
  obtain ⟨i, hi⟩ := (Factor.mem_support _ _).mp hw
  apply (mem_projectBag v bag w).mpr
  have hv : (retain v f h).scope i = w := hi
  have hv' : f.scope i = w.val := congrArg Subtype.val hv
  exact hbag ((Factor.mem_support _ _).mpr ⟨i, hv'⟩)

/-- The new bucket is covered by the projected leaf. -/
theorem support_bucketFactor_subset [CommSemiring R] [Fintype D]
    (bag : Finset V) (rest : List (Finset V))
    (fs : List (Factor V D R)) (covered : Bagged (bag :: rest) fs)
    (v : V) (hprivate : v ∈ privateVertices bag rest) :
    (bucketFactor v fs).support ⊆ projectBag v bag := by
  intro w hw
  obtain ⟨i, hi⟩ := (Factor.mem_support _ _).mp hw
  apply bucketVars_subset_leaf bag rest fs covered v hprivate
  apply List.mem_toFinset.mpr
  rw [← hi]
  exact List.get_mem _ _

/-- Factor coverage survives the actual materialized elimination step, including
outside occurrences, duplicates, zero factors and nullary tables. -/
theorem bagged_eliminate [CommSemiring R] [Fintype D] [LinearOrder D]
    (bag : Finset V) (rest : List (Finset V))
    (fs : List (Factor V D R)) (covered : Bagged (bag :: rest) fs)
    (v : V) (hprivate : v ∈ privateVertices bag rest) :
    Bagged ((bag :: rest).map (projectBag v)) (eliminate v fs) := by
  intro f hf
  simp only [eliminate, compileFactor_eq, List.mem_cons] at hf
  rcases hf with rfl | hf
  · exact ⟨projectBag v bag, by simp, support_bucketFactor_subset bag rest fs covered v hprivate⟩
  · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hf
    have holdfs : old.val ∈ fs := (List.mem_filter.mp old.property).1
    obtain ⟨b, hb, hsub⟩ := covered old.val holdfs
    exact ⟨projectBag v b, List.mem_map.mpr ⟨b, hb, rfl⟩,
      support_retain_subset v old.val _ b hsub⟩

end Counting.Algorithm.VariableEliminationWidth
