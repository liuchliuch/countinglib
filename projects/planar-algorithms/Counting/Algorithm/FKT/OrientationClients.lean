import Counting.Algorithm.FKT.Orientation

/-!
# Literal occurrence and raw-table clients

All finite computations below are checked by kernel `decide`. The examples
exercise repeated traversals, conflicting duplicate labels, and interacting
face equations whose reverse repair changes all three edge orientations.
-/

namespace Counting.Algorithm.FKT.Orientation.Clients

open PlanarHom.MultiGraph.Kasteleyn

/-- A bridge is traversed in both directions by the same boundary. -/
def bridgeDarts : List (Dart ℕ) := [(7, true), (7, false)]

/-- Replacing repeated edge occurrences by a single representative changes both
incidence parity and the clockwise-odd equation. -/
theorem bridge_multiplicity_matters :
    incidenceParity 7 bridgeDarts = false ∧
    incidenceParity 7 [(7, true)] = true ∧
    FaceOdd (fun _ : ℕ => false) bridgeDarts ∧
    ¬ FaceOdd (fun _ : ℕ => false) [(7, true)] := by
  unfold FaceOdd
  decide

/-- Conflicting rows with the same label are a raw input, not a valid materialized
boundary family. The first row is the one used by lookup. -/
def duplicateLabels : Table := [(1, [(7, false)]), (1, [(7, true)])]

/-- Reordering conflicting duplicate rows changes the actual result; the ignored
second row need not satisfy the computed orientation. -/
theorem duplicate_labels_use_first_row :
    tableBoundary duplicateLabels 1 = [(7, false)] ∧
    orientationLog duplicateLabels = [7] ∧
    orientationLog duplicateLabels.reverse = [] ∧
    FaceOdd (orientation duplicateLabels) [(7, false)] ∧
    ¬ FaceOdd (orientation duplicateLabels) [(7, true)] := by
  unfold FaceOdd
  decide

/-- Three interacting faces. Edge 10 borders the omitted root; edges 11 and 12
join consecutive listed faces. Their chronological pivots are 10, 11, and 12. -/
def threeFaces : Table :=
  [(1, [(10, false), (11, true)]),
   (2, [(11, false), (12, true)]),
   (3, [(12, false)])]

/-- Reverse repair propagates through all three faces; both implementations
produce the same exact ordered log. -/
theorem three_faces_compute :
    orientationLog threeFaces = [10, 11, 12] ∧
    iterativeLog threeFaces = [10, 11, 12] := by
  decide

/-- Every literal input boundary in the multi-face example is clockwise odd. -/
theorem three_faces_faceOdd :
    ∀ row ∈ threeFaces, FaceOdd (orientation threeFaces) row.2 := by
  intro row hrow
  simp only [threeFaces, List.mem_cons, List.not_mem_nil, or_false] at hrow
  unfold FaceOdd
  rcases hrow with rfl | rfl | rfl <;> decide

end Counting.Algorithm.FKT.Orientation.Clients
