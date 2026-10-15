import Paper2.Problem

/-! Serialization completeness and the zero/nullary/empty boundary cases belong
to the actual evaluation problem, independently of classification preprocessing. -/
namespace Paper2.Problem
open Paper2.ExactInput Paper2.Tractable Paper2.Complexity

/-- Every ordered finite labelled graph has an actual validated byte input. -/
def serializeInstance (L : Language) {S : NetworkShape 0}
    (labels : ClosedLabelling S L.count 1 L.arity) : Instance L :=
  ⟨labels.serialize, labels.serialize_wellFormed⟩

/-- The decoded value agrees with the original labelled graph, not just its size. -/
theorem value_serialize (w : Wiring) (L : Language) {S : NetworkShape 0}
    (labels : ClosedLabelling S L.count 1 L.arity) :
    value w L (serializeInstance L labels) =
      (labels.sourceNetwork L.signature (fun _ => w.kernel)).denote Fin.elim0 :=
  labels.denote_serialize L.signature (fun _ => w.kernel)

def emptyLabels (L : Language) : ClosedLabelling NetworkShape.empty L.count 1 L.arity where
  vertex := Fin.elim0
  vertex_arity v := Fin.elim0 v
  edge := Fin.elim0

def emptyInstance (L : Language) : Instance L := serializeInstance L (emptyLabels L)

@[simp] theorem value_empty (w : Wiring) (L : Language) : value w L (emptyInstance L) = 1 := by
  rw [emptyInstance, value_serialize]
  dsimp only [ClosedLabelling.sourceNetwork, emptyLabels, Network.denote, NetworkShape.empty]
  simp

/-- One isolated arity-zero vertex; no edge or incidence is fabricated. -/
def scalarShape : NetworkShape 0 where
  vertices := 1
  arity _ := 0
  edges := 0
  ports := {
    toFun p := Fin.elim0 p.2
    invFun p := Sum.elim Fin.elim0 (fun q => Fin.elim0 q.1) p
    left_inv p := Fin.elim0 p.2
    right_inv p := by
      cases p with
      | inl i => exact Fin.elim0 i
      | inr q => exact Fin.elim0 q.1 }

def scalarLabels (L : Language) (i : Fin L.count) (hi : L.arity i.val = 0) :
    ClosedLabelling scalarShape L.count 1 L.arity where
  vertex _ := i
  vertex_arity _ := hi
  edge := Fin.elim0

def scalarInstance (L : Language) (i : Fin L.count) (hi : L.arity i.val = 0) : Instance L :=
  serializeInstance L (scalarLabels L i hi)

/-- The actual isolated nullary vertex contributes exactly its scalar. -/
@[simp] theorem value_scalar (w : Wiring) (L : Language) (i : Fin L.count)
    (hi : L.arity i.val = 0) :
    value w L (scalarInstance L i hi) = L.signature i (fun j => Fin.elim0 (Fin.cast hi j)) := by
  rw [scalarInstance, value_serialize]
  dsimp only [ClosedLabelling.sourceNetwork, scalarLabels, Network.denote, scalarShape]
  simp
  congr 1
  funext j
  exact Fin.elim0 (Fin.cast hi j)

end Paper2.Problem
