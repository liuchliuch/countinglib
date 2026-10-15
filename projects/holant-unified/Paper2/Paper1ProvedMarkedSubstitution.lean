import Paper2.Paper1ProvedReplicationValidation

/-! Designated labels are counted through the actual fixed-gadget compiler.
The promise survives precisely when each fixed template retains its marked
label count; semantic equality of signatures never changes this count. -/
namespace Paper2.Paper1Proved.MarkedSubstitution
open Holant.Complexity Holant.Complexity.RawClosedNetwork
open Holant.Complexity.FixedGadgetSubstitution
set_option backward.isDefEq.respectTransparency false

def templateOccurrences (label : ℕ) (t : Template) : ℕ :=
  (t.vertices.filter (fun row => row.1==label)).length

theorem placed_count (label : ℕ) (t : Template) (offset : ℕ) (ports : List RawEndpoint) :
    FixedGadgetSubstitution.occurrences label ⟨t.placeVertices offset ports,[]⟩=templateOccurrences label t := by
  unfold FixedGadgetSubstitution.occurrences templateOccurrences Template.placeVertices
  have h (rows : List LocalVertex) :
      ((rows.map (fun row => (row.1,row.2.map (Template.placeEndpoint offset ports)))).filter
        (fun row => row.1==label)).length =
      (rows.filter (fun row => row.1==label)).length := by
    induction rows with
    | nil => rfl
    | cons row rows ih => by_cases hz : row.1=label <;> simp [hz,ih]
  exact h t.vertices

theorem expansion_count (label : ℕ) (templates : ℕ → Template) (offset : ℕ)
    (rows : List RawVertex) :
    FixedGadgetSubstitution.occurrences label (expandRows templates offset rows)=
      (rows.map (fun row => templateOccurrences label (templates row.1))).sum := by
  induction rows generalizing offset with
  | nil => rfl
  | cons row rows ih =>
    have hp := placed_count label (templates row.1) offset row.2
    change (((templates row.1).placeVertices offset row.2 ++
      (expandRows templates (offset+(templates row.1).edges.length) rows).vertices).filter
        (fun row => row.1==label)).length =
      templateOccurrences label (templates row.1) +
        (rows.map (fun row => templateOccurrences label (templates row.1))).sum
    rw [List.filter_append,List.length_append]
    change FixedGadgetSubstitution.occurrences label
        ⟨(templates row.1).placeVertices offset row.2,[]⟩ +
      FixedGadgetSubstitution.occurrences label
        (expandRows templates (offset+(templates row.1).edges.length) rows) = _
    rw [hp,ih]

theorem replace_count (label : ℕ) (templates : ℕ → Template) (r : RawClosedNetwork) :
    FixedGadgetSubstitution.occurrences label (replace templates r)=
      (r.vertices.map (fun row => templateOccurrences label (templates row.1))).sum :=
  expansion_count label templates r.edges.length r.vertices

theorem preserves (templates : ℕ → Template) (r : RawClosedNetwork)
    (h : ∀ row∈r.vertices, templateOccurrences 0 (templates row.1)=if row.1=0 then 1 else 0) :
    FixedGadgetSubstitution.occurrences 0 (replace templates r)=FixedGadgetSubstitution.occurrences 0 r := by
  rw [replace_count]
  have he : r.vertices.map (fun row => templateOccurrences 0 (templates row.1))=
      r.vertices.map (fun row => if row.1=0 then 1 else 0) := by
    apply List.map_congr_left
    exact h
  rw [he]
  exact Holant.Complexity.FixedGadgetSubstitution.Compiler.indicator_sum 0 r.vertices

end Paper2.Paper1Proved.MarkedSubstitution
