import Paper2.Complexity.BellMachines.RawTriple
import Paper2.BellReduction.NativeSmoothing.Raw

/-! Literal total list specification for the small native-X smoothing machine.
The first designated label-zero row is selected; valid binary rows are unique,
so filtering that row matches single indexed deletion. In a native graph every
edge label is zero, allowing faithful reconstruction after deletion. -/
namespace Paper2.Complexity.BellMachines.RawSmoothing
open Paper2.BellReduction.NativeSmoothing

 def row (G : RawClosedNetwork) : RawVertex := RawTriple.selected G 0
 def first (G : RawClosedNetwork) : RawEndpoint := (row G).2.getD 0 (0,false)
 def second (G : RawClosedNetwork) : RawEndpoint := (row G).2.getD 1 (0,false)
 def active (G : RawClosedNetwork) : Bool := (row G).2.length == 2
 def circle (G : RawClosedNetwork) : Bool := (first G).1 == (second G).1
 def remap (G : RawClosedNetwork) : RawEndpoint → RawEndpoint :=
   if circle G then Smoothing.removeLoopEndpoint (first G).1
   else Smoothing.spliceEndpoint (first G) (second G)
 def remaining (G : RawClosedNetwork) : List RawVertex := G.vertices.filter (fun v => v != row G)
 def query (G : RawClosedNetwork) : RawClosedNetwork where
   vertices := (remaining G).map (fun v => (v.1,v.2.map (remap G)))
   edges := List.replicate (G.edges.length-1) 0
 def compile (G : RawClosedNetwork) : Smoothing.Result :=
   if active G then ⟨query G,circle G⟩ else ⟨G,false⟩

end Paper2.Complexity.BellMachines.RawSmoothing
