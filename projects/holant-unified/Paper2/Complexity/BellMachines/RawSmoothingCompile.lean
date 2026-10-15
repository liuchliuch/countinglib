import Paper2.Complexity.BellMachines.RawSmoothing
import Paper2.Complexity.BellMachines.RawTripleCompile
import Paper2.Complexity.BellMachines.NaturalComparison
import Paper2.Complexity.BellMachines.NaturalSubtraction
import Paper2.Complexity.BellMachines.UnaryList

/-! Actual small Boolean-stack compiler for total native smoothing. Runtime
endpoint tests are canonical natural-word comparison/subtraction, and rows and
ports are processed by the checked physical framed-list traversals. -/
namespace Paper2.Complexity.BellMachines.RawSmoothing
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler Paper2.BellReduction.NativeSmoothing
open RawClosedNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
noncomputable section

abbrev rawEncoding := RawClosedNetwork.encoding
abbrev endsEncoding := framedListEncoding endpointEncoding
abbrev rowsEncoding := framedListEncoding vertexEncoding
abbrev contextEncoding := pairEncoding rawEncoding endpointEncoding

 def endpointIndex : Computes endpointEncoding encodingNatBool Prod.fst :=
  recode (Wiring.firstComputes encodingNatBool encodingBoolBool) id (fun _ => rfl) (fun _ => rfl)
 def endpointSide : Computes endpointEncoding encodingBoolBool Prod.snd :=
  recode (Wiring.secondComputes encodingNatBool encodingBoolBool) id (fun _ => rfl) (fun _ => rfl)
 def rowComputes : Computes rawEncoding vertexEncoding row := RawTriple.selectedComputes 0
 def firstComputes : Computes rawEncoding endpointEncoding first :=
  (rowComputes.andThen RawTriple.rowEndsComputes).andThen (getDComputes endpointEncoding 0 (0,false))
 def secondComputes : Computes rawEncoding endpointEncoding second :=
  (rowComputes.andThen RawTriple.rowEndsComputes).andThen (getDComputes endpointEncoding 1 (0,false))
 def firstIndexComputes : Computes rawEncoding encodingNatBool (fun G => (first G).1) :=
  firstComputes.andThen endpointIndex
 def secondIndexComputes : Computes rawEncoding encodingNatBool (fun G => (second G).1) :=
  secondComputes.andThen endpointIndex

 def activeComputes : Computes rawEncoding encodingBoolBool active := by
  let length := (rowComputes.andThen RawTriple.rowEndsComputes).andThen (Lists.lengthBinaryComputes endpointEncoding)
  exact congrComputes ((pairComputes length (constantComputes rawEncoding encodingNatBool 2)).andThen
    (Lists.equalComputes encodingNatBool)) (fun G => by simp only [active,beq_eq_decide,Function.comp_apply])
 def circleComputes : Computes rawEncoding encodingBoolBool circle :=
  congrComputes ((pairComputes firstIndexComputes secondIndexComputes).andThen
    (Lists.equalComputes encodingNatBool)) (fun G => by simp only [circle,beq_eq_decide,Function.comp_apply])

 def lowerEdgeComputes : Computes (pairEncoding encodingNatBool encodingNatBool) encodingNatBool
    (fun p => Smoothing.lowerEdge p.1 p.2) := by
  let current := Wiring.secondComputes encodingNatBool encodingNatBool
  let minus := (pairComputes current (constantComputes
    (pairEncoding encodingNatBool encodingNatBool) encodingNatBool 1)).andThen naturalSubtraction
  exact congrComputes (Lists.ifComputes naturalComparison minus current)
    (fun p => by simp [Smoothing.lowerEdge])

 def sourceGraph : Computes contextEncoding rawEncoding Prod.fst := Wiring.firstComputes _ _
 def currentEndpoint : Computes contextEncoding endpointEncoding Prod.snd := Wiring.secondComputes _ _
 def currentIndex := currentEndpoint.andThen endpointIndex
 def currentSide := currentEndpoint.andThen endpointSide
 def sourceFirst := sourceGraph.andThen firstComputes
 def sourceFirstIndex := sourceGraph.andThen firstIndexComputes
 def sourceSecondIndex := sourceGraph.andThen secondIndexComputes

 def loopComputes : Computes contextEncoding endpointEncoding
    (fun p => Smoothing.removeLoopEndpoint (first p.1).1 p.2) :=
  recode (pairComputes ((pairComputes sourceFirstIndex currentIndex).andThen lowerEdgeComputes)
    currentSide) id (fun _ => rfl) (fun _ => rfl)

 def spliceComputes : Computes contextEncoding endpointEncoding
    (fun p => Smoothing.spliceEndpoint (first p.1) (second p.1) p.2) := by
  let test := (pairComputes currentIndex sourceSecondIndex).andThen (Lists.equalComputes encodingNatBool)
  let yes : Computes contextEncoding endpointEncoding
      (fun p => (Smoothing.lowerEdge (second p.1).1 (first p.1).1,(first p.1).2)) :=
    recode (pairComputes ((pairComputes sourceSecondIndex sourceFirstIndex).andThen lowerEdgeComputes)
      (sourceFirst.andThen endpointSide)) id (fun _ => rfl) (fun _ => rfl)
  let no : Computes contextEncoding endpointEncoding
      (fun p => (Smoothing.lowerEdge (second p.1).1 p.2.1,p.2.2)) :=
    recode (pairComputes ((pairComputes sourceSecondIndex currentIndex).andThen lowerEdgeComputes)
      currentSide) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (Lists.ifComputes test yes no) (fun p => by simp [Smoothing.spliceEndpoint])

 def remapComputes : Computes contextEncoding endpointEncoding (fun p => remap p.1 p.2) :=
  congrComputes (Lists.ifComputes (sourceGraph.andThen circleComputes) loopComputes spliceComputes)
    (fun p => by cases h : circle p.1 <;> simp [remap,h])

 def remainingComputes : Computes rawEncoding rowsEncoding remaining :=
  (pairComputes (identityComputes rawEncoding) RawTriple.verticesComputes).andThen
    (Lists.filterComputes rawEncoding vertexEncoding (fun G v => v != row G)
      (RawTriple.unequalSelectedComputes 0))

 def mappedRowComputes : Computes (pairEncoding rawEncoding vertexEncoding) vertexEncoding
    (fun p => (p.2.1,p.2.2.map (remap p.1))) := by
  let graph := Wiring.firstComputes rawEncoding vertexEncoding
  let vertex := Wiring.secondComputes rawEncoding vertexEncoding
  let endpoints := (pairComputes graph (vertex.andThen RawTriple.rowEndsComputes)).andThen
    (Lists.mapListComputes rawEncoding endpointEncoding endpointEncoding remap remapComputes)
  exact recode (pairComputes (vertex.andThen RawTriple.rowLabelComputes) endpoints)
    id (fun _ => rfl) (fun _ => rfl)

 def remainingMappedComputes : Computes rawEncoding rowsEncoding
    (fun G => (remaining G).map (fun v => (v.1,v.2.map (remap G)))) :=
  (pairComputes (identityComputes rawEncoding) remainingComputes).andThen
    (Lists.mapListComputes rawEncoding vertexEncoding vertexEncoding
      (fun G v => (v.1,v.2.map (remap G))) mappedRowComputes)

 def shortenedEdgesComputes : Computes rawEncoding (framedListEncoding encodingNatBool)
    (fun G => List.replicate (G.edges.length-1) 0) :=
  ((RawTriple.edgesComputes.andThen (Lists.lengthUnaryComputes encodingNatBool)).andThen
    UnaryList.predecessor).andThen (UnaryList.replicateComputes encodingNatBool 0)

 def queryComputes : Computes rawEncoding rawEncoding query :=
  recode (pairComputes remainingMappedComputes shortenedEdgesComputes) id
    (fun _ => rfl) (fun _ => rfl)

 def resultEncoding : Encoding Smoothing.Result Bool where
  encode r := (pairEncoding rawEncoding encodingBoolBool).encode (r.query,r.circle)
  decode bits := ((pairEncoding rawEncoding encodingBoolBool).decode bits).map
    (fun p => ⟨p.1,p.2⟩)
  decode_encode r := by
    change Option.map _ ((pairEncoding rawEncoding encodingBoolBool).decode
      ((pairEncoding rawEncoding encodingBoolBool).encode (r.query,r.circle))) = some r
    rw [(pairEncoding rawEncoding encodingBoolBool).decode_encode]
    rfl

 def computes : Computes rawEncoding resultEncoding compile := by
  let yes : Computes rawEncoding resultEncoding (fun G => ⟨query G,circle G⟩) :=
    recode (pairComputes queryComputes circleComputes) id (fun _ => rfl) (fun _ => rfl)
  let no : Computes rawEncoding resultEncoding (fun G => ⟨G,false⟩) :=
    recode (pairComputes (identityComputes rawEncoding)
      (constantComputes rawEncoding encodingBoolBool false)) id (fun _ => rfl) (fun _ => rfl)
  exact Lists.ifComputes activeComputes yes no

end
end Paper2.Complexity.BellMachines.RawSmoothing
