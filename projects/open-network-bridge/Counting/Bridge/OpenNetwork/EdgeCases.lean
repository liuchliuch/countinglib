import Counting.Bridge.OpenNetwork.Corrected

/-! Empty domains are tested at the domain-general assignment lemma. The original
Holant object is Boolean; its empty-network case is tested separately. -/
noncomputable section
attribute [local instance] Classical.propDecidable
namespace Counting.Bridge.OpenNetwork.EdgeCases

open BoundaryComplement

def emptyBoundary : Empty ↪ Empty := Function.Embedding.refl Empty

def noBoundary : Empty ↪ Unit := ⟨Empty.elim, by intro a; exact Empty.elim a⟩

/-- Empty domain, empty boundary, and empty hidden type retain the single empty assignment. -/
theorem empty_domain_no_ports :
    (∑ _h : BoundaryComplement.Hidden emptyBoundary → Empty, (7 : Nat)) = 7 := by
  let : IsEmpty (BoundaryComplement.Hidden emptyBoundary) := ⟨fun h => Empty.elim h.val⟩
  simp

/-- Empty domain and a genuine hidden port have zero assignments. -/
theorem empty_domain_hidden_port :
    (∑ _h : BoundaryComplement.Hidden noBoundary → Empty, (7 : Nat)) = 0 := by
  let p : BoundaryComplement.Hidden noBoundary := ⟨(), by rintro ⟨e, _⟩; exact Empty.elim e⟩
  let : IsEmpty (BoundaryComplement.Hidden noBoundary → Empty) := ⟨fun h => Empty.elim (h p)⟩
  simp

/-- The sum-removal theorem applies to the empty domain without a chosen color. -/
theorem empty_domain_bridge :
    (∑ h : BoundaryComplement.Hidden noBoundary → Empty,
      (fun _ : Unit → Empty => (7 : Nat)) (extend noBoundary Empty.elim h)) =
      ∑ z : Unit → Empty, if ∀ j, z (noBoundary j) = Empty.elim j then 7 else 0 :=
  sum_extend noBoundary Empty.elim (fun _ => 7)

/-- A canonical empty OpenNetwork, including its explicit incidence obligations. -/
def empty : _root_.Holant.OpenNetwork Nat 0 where
  shape := {
    vertices := 0
    arity := Fin.elim0
    free := 0
    edges := 0
    boundary := ⟨Fin.elim0, by intro j; exact Fin.elim0 j⟩
    ends := ⟨fun e => Fin.elim0 e.1, by intro e; exact Fin.elim0 e.1⟩
    ordinary_boundary_iff_unpaired := fun p => Fin.elim0 p.1
    freeBoundary := Fin.elim0
    free_boundary := fun f => Fin.elim0 f
    freeEdge := Fin.elim0
    free_paired := fun f => Fin.elim0 f }
  vertex := fun v => Fin.elim0 v
  edge := Fin.elim0

theorem empty_raw (x : Fin 0 → Bool) : empty.raw x = 1 := by
  have hx : x = fun j => Fin.elim0 j := Subsingleton.elim _ _
  rw [hx]
  decide

theorem empty_partition (x : Fin 0 → Bool) : (toOpenInstance empty).partition x = 1 := by
  rw [partition_toOpenInstance, empty_raw]

theorem empty_corrected (x : Fin 0 → Bool) : (toTensorInstance empty).partition x = 1 := by
  rw [partition_tensor_eq_raw_closed, empty_partition]

end Counting.Bridge.OpenNetwork.EdgeCases
