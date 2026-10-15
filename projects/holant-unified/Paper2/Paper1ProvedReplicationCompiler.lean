import Paper2.Paper1ProvedUniversalPairProvider
import Holant.Proofs.Algorithms.QuaternaryReplicationCompiler
import Holant.Proofs.BinaryInterpolation.SingularExtraction.UnaryQuotient

/-! Actual finite byte compiler for the carrier copying chain. The closure
is fixed, each input carrier occurrence contributes exactly r native edges,
and every original ordered Y endpoint is retained. -/
noncomputable section
namespace Paper2.Paper1Proved.ReplicationCompiler
open Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient RawClosedNetwork FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option maxHeartbeats 2000000

structure Data where
  count : ℕ
  gArity : ℕ
  hArity : ℕ
  arity : ℕ → ℕ
  closure : Holant.Complexity.RawClosedNetwork
  seed : ℕ
namespace Data
 def sourceArity (D : Data) (i : ℕ) : ℕ := if i=0 then D.hArity else D.arity (i-1)
 def carrierArity (D : Data) (i : ℕ) : ℕ := if i=0 then D.gArity else D.arity (i-1)
 def targetArity (D : Data) (i : ℕ) : ℕ := if i=D.count+1 then D.gArity+(D.gArity+D.hArity)
   else D.carrierArity i
 def seedPorts (D : Data) : List RawEndpoint := (D.closure.vertices.getD D.seed (0,[])).2
end Data
variable (D : Data)
abbrev Input := ExactSignatureTables.Input (D.count+1) 1 D.sourceArity
abbrev RowQuery := FixedGadgetSubstitution.Compiler.Query (D.count+1) 1 D.sourceArity
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (D.count+1) 1 D.sourceArity
abbrev rowEncoding := queryEncoding (D.count+1) 1 D.sourceArity

def count (rows : List RawVertex) : ℕ := (rows.filter (fun row => row.1 == 0)).length
def before (x : RowQuery D) : ℕ := prefixWeight (D.count+1) 1 D.sourceArity
  (fun i => if i=0 then 1 else 0) x
def shift (m : ℕ) (p : RawEndpoint) : RawEndpoint := (m+p.1,p.2)
def carrierA (m t i : ℕ) : RawEndpoint := (m+D.closure.edges.length+D.gArity*t+i,true)
def carrierP (m k t i : ℕ) : RawEndpoint := if t+1=k then
  shift m (D.seedPorts.getD i (0,false)) else
    (m+D.closure.edges.length+D.gArity*(t+1)+i,false)

def sourceRow (m k t : ℕ) (row : RawVertex) : RawVertex := if row.1=0 then
  (D.count+1,(List.finRange D.gArity).map (fun i => carrierA D m t i.val) ++
    ((List.finRange D.gArity).map (fun i => carrierP D m k t i.val) ++ row.2)) else row

def closureRow (m k : ℕ) (row : RawVertex) : RawVertex :=
  (row.1,if row.1=0 ∧ k≠0 then (List.finRange D.gArity).map
    (fun i => (m+D.closure.edges.length+i.val,false)) else row.2.map (shift m))

def query (x : Input D) : Holant.Complexity.RawClosedNetwork where
  vertices := D.closure.vertices.map (closureRow D x.val.edges.length (count x.val.vertices)) ++
    (List.finRange x.val.vertices.length).map (fun v => sourceRow D x.val.edges.length
      (count x.val.vertices) (before D ⟨x,v⟩) (x.val.vertices.get v))
  edges := x.val.edges ++ D.closure.edges ++
    x.val.vertices.flatMap (fun row => if row.1=0 then List.replicate D.gArity 0 else [])

def countComputes : Computes (inputEncoding D) UnaryBinary.unaryEncoding
    (fun x => count x.val.vertices) := occurrencesComputes (D.count+1) 1 D.sourceArity 0
 def countBinary : Computes (inputEncoding D) encodingNatBool (fun x => count x.val.vertices) :=
  (countComputes D).andThen UnaryBinary.computes
 def edgeBinary : Computes (inputEncoding D) encodingNatBool (fun x => x.val.edges.length) :=
  (edgeCountComputes (D.count+1) 1 D.sourceArity).andThen UnaryBinary.computes
 def beforeBinary : Computes (rowEncoding D) encodingNatBool (before D) :=
  (prefixWeightComputes (D.count+1) 1 D.sourceArity (fun i => if i=0 then 1 else 0)).andThen UnaryBinary.computes
 def rowEdgeBinary : Computes (rowEncoding D) encodingNatBool (fun x => x.1.val.edges.length) :=
  (sourceComputes (D.count+1) 1 D.sourceArity).andThen (edgeBinary D)
 def rowCountBinary : Computes (rowEncoding D) encodingNatBool (fun x => count x.1.val.vertices) :=
  (sourceComputes (D.count+1) 1 D.sourceArity).andThen (countBinary D)
 def rowPorts : Computes (rowEncoding D) (framedListEncoding endpointEncoding)
    (fun x => (x.1.val.vertices.get x.2).2) :=
  (originalRowComputes (D.count+1) 1 D.sourceArity).andThen
    (recode (Wiring.secondComputes encodingNatBool (framedListEncoding endpointEncoding))
      id (fun _ => rfl) (fun _ => rfl))

def times {A : Type} (e : Encoding A Bool) (t : A → ℕ)
    (wt : Computes e encodingNatBool t) (r : ℕ) :
    Computes e encodingNatBool (fun x => r*t x) := by
  induction r with
  | zero => exact congrComputes (constantComputes e encodingNatBool 0) (fun x => by simp)
  | succ r ih =>
      exact congrComputes (QuaternaryReplicationCompiler.add wt ih)
        (fun x => by simp [Nat.succ_mul,Nat.add_comm])
def shifted {A : Type} (e : Encoding A Bool) (m : A → ℕ)
    (wm : Computes e encodingNatBool m) (p : RawEndpoint) :
    Computes e endpointEncoding (fun x => shift (m x) p) :=
  recode (pairComputes (QuaternaryReplicationCompiler.add wm (constantComputes e encodingNatBool p.1))
    (constantComputes e encodingBoolBool p.2)) id (fun _ => rfl) (fun _ => rfl)
def fresh {A : Type} (e : Encoding A Bool) (m t : A → ℕ)
    (wm : Computes e encodingNatBool m) (wt : Computes e encodingNatBool t)
    (i : ℕ) (side : Bool) : Computes e endpointEncoding
    (fun x => (m x+D.closure.edges.length+D.gArity*t x+i,side)) :=
  recode (pairComputes (QuaternaryReplicationCompiler.add
    (QuaternaryReplicationCompiler.add (QuaternaryReplicationCompiler.add wm
      (constantComputes e encodingNatBool D.closure.edges.length)) (times e t wt D.gArity))
        (constantComputes e encodingNatBool i)) (constantComputes e encodingBoolBool side))
      id (fun _ => rfl) (fun _ => rfl)

 def carrierAComputes (i : Fin D.gArity) : Computes (rowEncoding D) endpointEncoding
    (fun x => carrierA D x.1.val.edges.length (before D x) i.val) :=
  fresh D (rowEncoding D) (fun x => x.1.val.edges.length) (before D)
    (rowEdgeBinary D) (beforeBinary D) i.val true
 def carrierPComputes (i : Fin D.gArity) : Computes (rowEncoding D) endpointEncoding
    (fun x => carrierP D x.1.val.edges.length (count x.1.val.vertices) (before D x) i.val) := by
  let t := QuaternaryReplicationCompiler.add (beforeBinary D) (constantComputes (rowEncoding D) encodingNatBool 1)
  let test := (pairComputes t (rowCountBinary D)).andThen
    UniversalPairReduction.SmoothingCompiler.Endpoints.equalComputes
  let last := shifted (rowEncoding D) (fun x => x.1.val.edges.length) (rowEdgeBinary D)
    (D.seedPorts.getD i.val (0,false))
  let next := fresh D (rowEncoding D) (fun x => x.1.val.edges.length)
    (fun x => before D x+1) (rowEdgeBinary D) t i.val false
  exact congrComputes (UniversalPairReduction.SmoothingCompiler.ifComputes test last next)
    (fun x => by simp [carrierP,test,Function.comp_def])

 def replacedRowComputes : Computes (rowEncoding D) vertexEncoding
    (fun x => (D.count+1,(List.finRange D.gArity).map (fun i => carrierA D x.1.val.edges.length (before D x) i.val) ++
      ((List.finRange D.gArity).map (fun i => carrierP D x.1.val.edges.length (count x.1.val.vertices)
        (before D x) i.val) ++ (x.1.val.vertices.get x.2).2))) := by
  let ae := (fixedListComputes (rowEncoding D) endpointEncoding
    (fun x i => carrierA D x.1.val.edges.length (before D x) i.val)
      (carrierAComputes D) (List.finRange D.gArity)).andThen (entriesComputes endpointEncoding)
  let pe := (fixedListComputes (rowEncoding D) endpointEncoding
    (fun x i => carrierP D x.1.val.edges.length (count x.1.val.vertices) (before D x) i.val)
      (carrierPComputes D) (List.finRange D.gArity)).andThen (entriesComputes endpointEncoding)
  let ye := (rowPorts D).andThen (entriesComputes endpointEncoding)
  let ports : Computes (rowEncoding D) (framedListEncoding endpointEncoding)
      (fun x => (List.finRange D.gArity).map (fun i => carrierA D x.1.val.edges.length (before D x) i.val) ++
        ((List.finRange D.gArity).map (fun i => carrierP D x.1.val.edges.length (count x.1.val.vertices)
          (before D x) i.val) ++ (x.1.val.vertices.get x.2).2)) :=
    recode (joinComputes (joinComputes ae (joinComputes pe ye))
      (constantComputes (rowEncoding D) Frame.wordEncoding [false])) id (fun _ => rfl)
      (fun x => by
        change (_++_)++[false] = framedListEncode endpointEncoding
          ((List.finRange D.gArity).map (fun i => carrierA D x.1.val.edges.length (before D x) i.val) ++
            ((List.finRange D.gArity).map (fun i => carrierP D x.1.val.edges.length (count x.1.val.vertices)
              (before D x) i.val) ++ (x.1.val.vertices.get x.2).2))
        have h := entries_append_encode endpointEncoding
          ((List.finRange D.gArity).map (fun i => carrierA D x.1.val.edges.length (before D x) i.val) ++
            ((List.finRange D.gArity).map (fun i => carrierP D x.1.val.edges.length (count x.1.val.vertices)
              (before D x) i.val) ++ (x.1.val.vertices.get x.2).2)) []
        simpa [entries,List.flatMap_append,List.append_assoc,framedListEncode] using h)
  exact recode (pairComputes (constantComputes (rowEncoding D) encodingNatBool (D.count+1)) ports)
    id (fun _ => rfl) (fun _ => rfl)

 def sourceRowComputes : Computes (rowEncoding D) vertexEncoding
    (fun x => sourceRow D x.1.val.edges.length (count x.1.val.vertices) (before D x) (x.1.val.vertices.get x.2)) := by
  apply congrComputes (chooseComputes (rowEncoding D) vertexEncoding (D.count+1)
    (sourceLabel (D.count+1) 1 D.sourceArity)
    (fun x i => if i.val=0 then (D.count+1,
      (List.finRange D.gArity).map (fun i => carrierA D x.1.val.edges.length (before D x) i.val) ++
      ((List.finRange D.gArity).map (fun i => carrierP D x.1.val.edges.length (count x.1.val.vertices)
        (before D x) i.val) ++ (x.1.val.vertices.get x.2).2)) else x.1.val.vertices.get x.2)
    (labelRecodeComputes (D.count+1) 1 D.sourceArity UnaryBinary.unaryEncoding Fin.val)
    (fun i => by
      by_cases hi : i.val=0
      · exact congrComputes (replacedRowComputes D) (fun x => by simp [hi])
      · exact congrComputes (originalRowComputes (D.count+1) 1 D.sourceArity) (fun x => by simp [hi])))
  intro x
  simp [sourceRow,sourceLabel]

 def closureRowComputes (row : RawVertex) : Computes (inputEncoding D) vertexEncoding
    (fun x => closureRow D x.val.edges.length (count x.val.vertices) row) := by
  let shiftedPorts := fixedListComputes (inputEncoding D) endpointEncoding
    (fun x p => shift x.val.edges.length p)
    (fun p => shifted (inputEncoding D) (fun x => x.val.edges.length) (edgeBinary D) p) row.2
  by_cases hz : row.1=0
  · let freshPorts := fixedListComputes (inputEncoding D) endpointEncoding
      (fun (x : Input D) (i : Fin D.gArity) => (x.val.edges.length+D.closure.edges.length+i.val,false))
      (fun i => congrComputes (fresh D (inputEncoding D) (fun x => x.val.edges.length) (fun _ => 0)
        (edgeBinary D) (constantComputes (inputEncoding D) encodingNatBool 0) i.val false)
          (fun x => by simp))
      (List.finRange D.gArity)
    let test := (pairComputes (countBinary D) (constantComputes (inputEncoding D) encodingNatBool 0)).andThen
      UniversalPairReduction.SmoothingCompiler.Endpoints.equalComputes
    let ports := UniversalPairReduction.SmoothingCompiler.ifComputes test shiftedPorts freshPorts
    exact congrComputes (recode (pairComputes (constantComputes (inputEncoding D) encodingNatBool row.1) ports)
      id (fun _ => rfl) (fun _ => rfl)) (fun x => by simp [closureRow,hz])
  · exact congrComputes (recode (pairComputes (constantComputes (inputEncoding D) encodingNatBool row.1) shiftedPorts)
      id (fun _ => rfl) (fun _ => rfl)) (fun x => by simp [closureRow,hz])

 def verticesComputes : Computes (inputEncoding D) (framedListEncoding vertexEncoding)
    (fun x => (query D x).vertices) := by
  let head := (fixedListComputes (inputEncoding D) vertexEncoding
    (fun x row => closureRow D x.val.edges.length (count x.val.vertices) row)
    (closureRowComputes D) D.closure.vertices).andThen (entriesComputes vertexEncoding)
  let body := allRowsFlatMapComputes (D.count+1) 1 D.sourceArity _
    ((sourceRowComputes D).andThen (entryComputes vertexEncoding))
  refine recode (joinComputes (joinComputes head body)
    (constantComputes (inputEncoding D) Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro x
  change (_++_)++[false] = framedListEncode vertexEncoding (query D x).vertices
  have h := entries_append_encode vertexEncoding (query D x).vertices []
  simpa [query,entries,List.flatMap_append,List.flatMap_map,Function.comp_def,framedListEncode,List.append_assoc] using h

 def edgesComputes : Computes (inputEncoding D) (framedListEncoding encodingNatBool)
    (fun x => (query D x).edges) := by
  let old := (FixedGadgetSubstitution.Compiler.edgesComputes (D.count+1) 1 D.sourceArity).andThen
    (entriesComputes encodingNatBool)
  let seed := constantComputes (inputEncoding D) Frame.wordEncoding (entries encodingNatBool D.closure.edges)
  let added := allRowsFlatMapComputes (D.count+1) 1 D.sourceArity _
    (labelRecodeComputes (D.count+1) 1 D.sourceArity Frame.wordEncoding
      (fun i => entries encodingNatBool (if i.val=0 then List.replicate D.gArity 0 else [])))
  refine recode (joinComputes (joinComputes (joinComputes old seed) added)
    (constantComputes (inputEncoding D) Frame.wordEncoding [false])) id (fun _ => rfl) ?_
  intro x
  change ((entries encodingNatBool x.val.edges ++ entries encodingNatBool D.closure.edges) ++ _) ++ [false] = framedListEncode encodingNatBool (query D x).edges
  have ha : (List.finRange x.val.vertices.length).flatMap
      (fun v => entries encodingNatBool (if (x.val.vertices.get v).1=0 then List.replicate D.gArity 0 else [])) =
      entries encodingNatBool (x.val.vertices.flatMap (fun row => if row.1=0 then List.replicate D.gArity 0 else [])) := by
    rw [← entries_flatMap]
    congr 1
    have h := congrArg (fun rows : List RawVertex => rows.flatMap
      (fun row => if row.1=0 then List.replicate D.gArity 0 else []))
        (all_rows (D.count+1) 1 D.sourceArity x)
    simpa only [List.flatMap_map,Function.comp_def] using h
  dsimp only [id_eq,sourceLabel]
  rw [ha]
  have h := entries_append_encode encodingNatBool (query D x).edges []
  simpa [query,entries,List.flatMap_append,framedListEncode,List.append_assoc] using h

 def rawComputes : Computes (inputEncoding D) RawClosedNetwork.encoding (query D) :=
  recode (pairComputes (verticesComputes D) (edgesComputes D)) id (fun _ => rfl) (fun _ => rfl)

end Paper2.Paper1Proved.ReplicationCompiler
