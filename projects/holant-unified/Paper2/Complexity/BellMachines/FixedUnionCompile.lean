import Paper2.Complexity.BellMachines.RawTripleCompile
import Paper2.BellReduction.RawDisjointUnion

/-! Append a fixed witness graph through an actual original-byte machine.
The fixed witness's endpoint addresses are shifted by the runtime original edge
count using canonical binary addition. Every original component is retained. -/
namespace Paper2.Complexity.BellMachines.FixedUnion
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler RawClosedNetwork Paper2.BellReduction.RawDisjointUnion
noncomputable section

 def shiftedEnd (p : RawEndpoint) : Computes RawClosedNetwork.encoding endpointEncoding
    (fun G => shiftEnd G.edges.length p) :=
  recode (pairComputes
    ((pairComputes RawTriple.edgeCountComputes
      (constantComputes RawClosedNetwork.encoding encodingNatBool p.1)).andThen naturalAddition)
    (constantComputes RawClosedNetwork.encoding encodingBoolBool p.2)) id (fun _ => rfl) (fun _ => rfl)

 def shiftedRow (v : RawVertex) : Computes RawClosedNetwork.encoding vertexEncoding
    (fun G => shiftRow G.edges.length v) :=
  recode (pairComputes (constantComputes RawClosedNetwork.encoding encodingNatBool v.1)
    (fixedListComputes RawClosedNetwork.encoding endpointEncoding
      (fun G p => shiftEnd G.edges.length p) shiftedEnd v.2)) id (fun _ => rfl) (fun _ => rfl)

 def computes (W : RawClosedNetwork) : Computes RawClosedNetwork.encoding RawClosedNetwork.encoding
    (fun G => union G W) := by
  let newRows := fixedListComputes RawClosedNetwork.encoding vertexEncoding
    (fun G v => shiftRow G.edges.length v) shiftedRow W.vertices
  let rows := (pairComputes RawTriple.verticesComputes newRows).andThen
    (Lists.appendListsComputes vertexEncoding)
  let edges := RawTriple.edgesComputes.andThen (appendComputes encodingNatBool W.edges)
  exact recode (pairComputes rows edges) id (fun _ => rfl) (fun _ => rfl)

end
end Paper2.Complexity.BellMachines.FixedUnion
