import Paper2.Complexity.BellMachines.RawTripleCompile
import Paper2.BellReduction.RawTripleBridge

/-! The real raw graph program, now on valid original instances. Subtype proofs
add no input or output bits; the program, time polynomial and literal output
records are exactly those of `RawTriple.computes`. -/
set_option maxRecDepth 8192
namespace Paper2.Complexity.BellMachines.RawTriple
open Computability BinaryCompose FixedFieldMachines Paper2.Problem Paper2.ExactInput
open Paper2.BellReduction.RawOccurrence Paper2.BellReduction.RawTripleBridge
noncomputable section

abbrev TripleInstance (L : Language) :=
  { G : Instance L // 3 ≤ markedCount G.val.vertices }

def tripleEncoding (L : Language) : Encoding (TripleInstance L) Bool where
  encode G := (inputEncoding L).encode G.val
  decode bits := ((inputEncoding L).decode bits).bind
    (fun G => if h : 3 ≤ markedCount G.val.vertices then some ⟨G,h⟩ else none)
  decode_encode G := by simp [G.property]

def transformValid (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (G : TripleInstance L) : Instance L :=
  ⟨transform coreLabel G.val.val,
    machine_wellFormed G.val.property hzero G.property coreLabel hl ha⟩

/-- No validator or semantic table is evaluated as a host-language instruction.
The actual machine is the already compiled raw row/edge program. -/
def validComputes (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8) :
    Computes (tripleEncoding L) (inputEncoding L)
      (transformValid L hzero coreLabel hl ha) :=
  recode (computes coreLabel) (fun G => G.val.val) (fun _ => rfl) (fun _ => rfl)

theorem valid_count (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (G : TripleInstance L) :
    markedCount (transformValid L hzero coreLabel hl ha G).val.vertices + 2 =
      markedCount G.val.val.vertices := by
  have hn : coreLabel ≠ 0 := by intro h; subst coreLabel; omega
  exact perform_count _ _ _ hn (splitThree_machine G.val.property hzero G.property)

theorem valid_vertices (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (G : TripleInstance L) :
    (transformValid L hzero coreLabel hl ha G).val.vertices.length + 1 =
      G.val.val.vertices.length :=
  perform_vertices _ _ _ (splitThree_machine G.val.property hzero G.property)

theorem valid_edges (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (G : TripleInstance L) :
    (transformValid L hzero coreLabel hl ha G).val.edges.length =
      G.val.val.edges.length + 2 := perform_edges _ _ _

end
end Paper2.Complexity.BellMachines.RawTriple
