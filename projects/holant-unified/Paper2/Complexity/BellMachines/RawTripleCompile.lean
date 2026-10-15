import Paper2.Complexity.BellMachines.RawTriple
import Paper2.Complexity.BellMachines.ListOperations
import Paper2.Complexity.BellMachines.NaturalAddition

/-! Actual polynomial-bit-time compiler of the literal three-Bell-to-one raw
surgery. Labels and endpoints are read from the original raw graph encoding.
The output is exactly RawTriple.transform, including its unchanged old edges.
Validity and partition-function correspondence are separate mathematical bridges.
-/
namespace Paper2.Complexity.BellMachines.RawTriple
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open RawClosedNetwork
noncomputable section

abbrev rawEncoding := RawClosedNetwork.encoding
abbrev rowsEncoding := framedListEncoding vertexEncoding
abbrev endsEncoding := framedListEncoding endpointEncoding
abbrev edgesEncoding := framedListEncoding encodingNatBool

/-- Real projections from the original graph codec, with no input recoding. -/
def verticesComputes : Computes rawEncoding rowsEncoding RawClosedNetwork.vertices :=
  recode (Wiring.firstComputes rowsEncoding edgesEncoding)
    (fun G => (G.vertices, G.edges)) (fun _ => rfl) (fun _ => rfl)

def edgesComputes : Computes rawEncoding edgesEncoding RawClosedNetwork.edges :=
  recode (Wiring.secondComputes rowsEncoding edgesEncoding)
    (fun G => (G.vertices, G.edges)) (fun _ => rfl) (fun _ => rfl)

def rowLabelComputes : Computes vertexEncoding encodingNatBool Prod.fst :=
  recode (Wiring.firstComputes encodingNatBool endsEncoding) id (fun _ => rfl) (fun _ => rfl)

def rowEndsComputes : Computes vertexEncoding endsEncoding Prod.snd :=
  recode (Wiring.secondComputes encodingNatBool endsEncoding) id (fun _ => rfl) (fun _ => rfl)

def markedTest : Computes vertexEncoding encodingBoolBool (fun v : RawVertex => v.1 == 0) :=
  congrComputes
    ((pairComputes rowLabelComputes (constantComputes vertexEncoding encodingNatBool 0)).andThen
      (Lists.equalComputes encodingNatBool))
    (fun v => by simp only [Function.comp_apply, beq_eq_decide])

def markedComputes : Computes rawEncoding rowsEncoding marked := by
  let prepare := pairComputes (constantComputes rawEncoding encodingBoolBool false) verticesComputes
  let test := (Wiring.secondComputes encodingBoolBool vertexEncoding).andThen markedTest
  exact prepare.andThen (Lists.filterComputes encodingBoolBool vertexEncoding (fun _ v => v.1 == 0) test)

def selectedComputes (i : ℕ) : Computes rawEncoding vertexEncoding (fun G => selected G i) :=
  markedComputes.andThen (getDComputes vertexEncoding i (0, []))

def notComputes : Computes encodingBoolBool encodingBoolBool Bool.not :=
  FiniteRecode.computes encodingBoolBool encodingBoolBool Bool.not 1 (fun b => by cases b <;> decide)

def andComputes : Computes (pairEncoding encodingBoolBool encodingBoolBool)
    encodingBoolBool (fun p => p.1 && p.2) :=
  FiniteRecode.computes (pairEncoding encodingBoolBool encodingBoolBool) encodingBoolBool
    (fun p => p.1 && p.2) 4 (fun p => by rcases p with ⟨a,b⟩; cases a <;> cases b <;> decide)

abbrev rowContextEncoding := pairEncoding rawEncoding vertexEncoding

def unequalSelectedComputes (i : ℕ) : Computes rowContextEncoding encodingBoolBool
    (fun p => p.2 != selected p.1 i) := by
  let current := Wiring.secondComputes rawEncoding vertexEncoding
  let selected := (Wiring.firstComputes rawEncoding vertexEncoding).andThen (selectedComputes i)
  let equal := (pairComputes current selected).andThen (Lists.equalComputes vertexEncoding)
  exact congrComputes (equal.andThen notComputes) (fun p => by simp only [Function.comp_apply, bne, beq_eq_decide])

def keepComputes : Computes rowContextEncoding encodingBoolBool
    (fun p => keep (selected p.1 0) (selected p.1 1) (selected p.1 2) p.2) :=
  ((pairComputes
    ((pairComputes (unequalSelectedComputes 0) (unequalSelectedComputes 1)).andThen andComputes)
    (unequalSelectedComputes 2)).andThen andComputes)

def restComputes : Computes rawEncoding rowsEncoding rest :=
  (pairComputes (identityComputes rawEncoding) verticesComputes).andThen
    (Lists.filterComputes rawEncoding vertexEncoding
      (fun G v => keep (selected G 0) (selected G 1) (selected G 2) v) keepComputes)

def selectedEndsComputes (i : ℕ) : Computes rawEncoding endsEncoding (fun G => (selected G i).2) :=
  (selectedComputes i).andThen rowEndsComputes

def edgeCountComputes : Computes rawEncoding encodingNatBool (fun G => G.edges.length) :=
  edgesComputes.andThen (Lists.lengthBinaryComputes encodingNatBool)

def nextEdgeComputes : Computes rawEncoding encodingNatBool (fun G => G.edges.length + 1) :=
  (pairComputes edgeCountComputes (constantComputes rawEncoding encodingNatBool 1)).andThen naturalAddition

def newEndpointComputes (side next : Bool) : Computes rawEncoding endpointEncoding
    (fun G => (if next then G.edges.length + 1 else G.edges.length, side)) := by
  let index : Computes rawEncoding encodingNatBool
      (fun G => if next then G.edges.length + 1 else G.edges.length) := by
    cases next
    · exact edgeCountComputes
    · exact nextEdgeComputes
  exact recode (pairComputes index (constantComputes rawEncoding encodingBoolBool side))
    id (fun _ => rfl) (fun _ => rfl)

def newEndsComputes (side : Bool) : Computes rawEncoding endsEncoding
    (fun G => [(G.edges.length,side), (G.edges.length+1,side)]) := by
  exact congrComputes
    (fixedListComputes rawEncoding endpointEncoding
      (fun G next => (if next then G.edges.length+1 else G.edges.length,side))
      (newEndpointComputes side) [false,true]) (fun G => rfl)

def appendEnds {f g : RawClosedNetwork → List RawEndpoint}
    (u : Computes rawEncoding endsEncoding f) (v : Computes rawEncoding endsEncoding g) :
    Computes rawEncoding endsEncoding (fun G => f G ++ g G) :=
  (pairComputes u v).andThen (Lists.appendListsComputes endpointEncoding)

def coreEndsComputes : Computes rawEncoding endsEncoding
    (fun G => [(G.edges.length,false),(G.edges.length+1,false)] ++
      (selected G 0).2 ++ (selected G 1).2 ++ (selected G 2).2) :=
  appendEnds (appendEnds (appendEnds (newEndsComputes false)
    (selectedEndsComputes 0)) (selectedEndsComputes 1)) (selectedEndsComputes 2)

def coreRowComputes (coreLabel : ℕ) : Computes rawEncoding vertexEncoding
    (fun G => (coreLabel,[(G.edges.length,false),(G.edges.length+1,false)] ++
      (selected G 0).2 ++ (selected G 1).2 ++ (selected G 2).2)) :=
  recode (pairComputes (constantComputes rawEncoding encodingNatBool coreLabel) coreEndsComputes)
    id (fun _ => rfl) (fun _ => rfl)

def bellRowComputes : Computes rawEncoding vertexEncoding
    (fun G => (0,[(G.edges.length,true),(G.edges.length+1,true)])) :=
  recode (pairComputes (constantComputes rawEncoding encodingNatBool 0) (newEndsComputes true))
    id (fun _ => rfl) (fun _ => rfl)

def newRowsComputes (coreLabel : ℕ) : Computes rawEncoding rowsEncoding
    (fun G => [(coreLabel,[(G.edges.length,false),(G.edges.length+1,false)] ++
      (selected G 0).2 ++ (selected G 1).2 ++ (selected G 2).2),
      (0,[(G.edges.length,true),(G.edges.length+1,true)])]) := by
  let f (G : RawClosedNetwork) (next : Bool) : RawVertex :=
    if next then (0,[(G.edges.length,true),(G.edges.length+1,true)]) else
      (coreLabel,[(G.edges.length,false),(G.edges.length+1,false)] ++
        (selected G 0).2 ++ (selected G 1).2 ++ (selected G 2).2)
  let cell (next : Bool) : Computes rawEncoding vertexEncoding (fun G => f G next) := by
    cases next
    · exact coreRowComputes coreLabel
    · exact bellRowComputes
  exact congrComputes (fixedListComputes rawEncoding vertexEncoding f cell [false,true])
    (fun G => rfl)

/-- Actual graph serializer after runtime list surgery, not a semantic graph as
an auxiliary input. Its time polynomial is measured in original graph bytes. -/
def computes (coreLabel : ℕ) : Computes rawEncoding rawEncoding (transform coreLabel) := by
  let vertices := (pairComputes restComputes (newRowsComputes coreLabel)).andThen
    (Lists.appendListsComputes vertexEncoding)
  let edges := edgesComputes.andThen (appendComputes encodingNatBool [0,0])
  exact recode (pairComputes vertices edges) id (fun _ => rfl) (fun _ => rfl)

theorem inFP (coreLabel : ℕ) : InFP rawEncoding rawEncoding (transform coreLabel) :=
  (computes coreLabel).inFP

end
end Paper2.Complexity.BellMachines.RawTriple
