import Counting.Model.Graph
import Counting.Upstream.PlanarHom

/-!
# Bridge from the pinned original PlanarHom partition function

`Counting.Upstream.PlanarHom` is the unchanged `PlanarHom/Basic.lean` at commit
`db68e745380769c38c8347736d2d84fcde38263c`. This module translates its actual
`PlanarHom.MultiGraph.partition`, preserving the vertex and edge types.
-/

noncomputable section

namespace Counting.Bridge.PlanarHom

open Counting.Model

open Classical

variable {V E D R : Type}

/-- Keep the original vertex type, edge occurrence type, and ordered endpoints. -/
def toModel (G : _root_.PlanarHom.MultiGraph V E) : Model.MultiGraph V E :=
  ⟨G.src, G.dst⟩

/-- The upstream uniform background is a special case of vertex-specific weights. -/
theorem assignmentWeight_eq [Fintype V] [Fintype E] [CommSemiring R]
    (G : _root_.PlanarHom.MultiGraph V E) (M : D → D → R) (w : D → R) (a : V → D) :
    (toModel G).assignmentWeight M (fun _ => w) a = G.assignmentWeight M w a := rfl

/-- Equality with the original upstream partition declaration. -/
theorem partition_eq [Fintype V] [Fintype E] [Fintype D] [CommSemiring R]
    (G : _root_.PlanarHom.MultiGraph V E) (M : D → D → R) (w : D → R) :
    (toModel G).partition M (fun _ => w) = G.partition M w := rfl

/-- The upstream graph as an occurrence instance, with its uniform vertex table. -/
def toOpenInstance [Fintype V] [Fintype E]
    (G : _root_.PlanarHom.MultiGraph V E) (M : D → D → R) (w : D → R) :
    OpenInstance (Model.MultiGraph.graphLanguage M (fun _ : V => w)) Empty V :=
  (toModel G).toOpenInstance M (fun _ => w)

/-- The actual pinned upstream graph partition agrees with the common CSP
semantics for all instances, including loops, parallel edges, and isolated vertices. -/
theorem partition_toOpenInstance [Fintype V] [Fintype E] [Fintype D] [CommSemiring R]
    (G : _root_.PlanarHom.MultiGraph V E) (M : D → D → R) (w : D → R)
    (a : Empty → D) :
    (toOpenInstance G M w).partition a = G.partition M w := by
  exact (Model.MultiGraph.partition_toOpenInstance (toModel G) M (fun _ => w) a).trans
    (partition_eq G M w)

end Counting.Bridge.PlanarHom
