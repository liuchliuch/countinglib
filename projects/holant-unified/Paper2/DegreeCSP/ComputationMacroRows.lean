import Paper2.DegreeCSP.ComputationMacroPorts

/-! The variable macro is emitted by two actual unary-indexed scans: the main
rows, then the ordered connector pairs. Degree zero retains its two closed rows. -/
namespace Paper2.DegreeCSP.ComputationRecords.Emit
open Holant Holant.Algebraic Holant.Complexity Computability
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.Complexity.GraphPreprocessing Holant.Complexity.GraphPreprocessing.OriginalCoefficient
open Holant.Complexity.FixedGadgetSubstitution Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Program
open ComputationLayout
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

def mainCount (k : ℕ) (x : Records.Variable) := ComputationLayout.multiplicity k (Raw.degree x.1 x.2.val)
def connectorCount (k : ℕ) (x : Records.Variable) := mainCount k x-1

def mainRowComputes (k : ℕ) (hk : 0<k) (label : ℕ) :
    Computes (blockEncoding (mainCount k)) RawClosedNetwork.vertexEncoding (fun x=>
      (label,List.ofFn (fun j : Fin k=>mainEndpoint k (mainCount k x.1)
        (outerOffsetRaw x.1.1 x.1.2.val) (innerOffsetRaw k x.1.1 x.1.2.val) x.2.val j.val))) :=
  fixedRowComputes _ k label _ (mainEndpointComputes (mainCount k) k hk)

def firstConnectorRowComputes (k : ℕ) (hk : 0<k) (label : ℕ) :
    Computes (blockEncoding (connectorCount k)) RawClosedNetwork.vertexEncoding (fun x=>
      (label,List.ofFn (fun j : Fin k=>firstConnectorEndpoint k
        (outerOffsetRaw x.1.1 x.1.2.val) (innerOffsetRaw k x.1.1 x.1.2.val) x.2.val j.val))) :=
  fixedRowComputes _ k label _ (firstConnectorEndpointComputes (connectorCount k) k hk)

def secondConnectorRowComputes (k : ℕ) (hk : 0<k) (label : ℕ) :
    Computes (blockEncoding (connectorCount k)) RawClosedNetwork.vertexEncoding (fun x=>
      (label,List.ofFn (fun j : Fin k=>secondConnectorEndpoint k
        (innerOffsetRaw k x.1.1 x.1.2.val) x.2.val j.val))) :=
  fixedRowComputes _ k label _ (secondConnectorEndpointComputes (connectorCount k) k hk)

def zeroRowComputes (k : ℕ) (hk : 0<k) (label : ℕ) (b : Bool) :
    Computes Records.variableEncoding RawClosedNetwork.vertexEncoding (fun x=>
      (label,List.ofFn (fun j : Fin k=>(innerOffsetRaw k x.1 x.2.val+j.val,b)))) :=
  fixedRowComputes _ k label _ (zeroEndpointComputes k hk b)

def positiveEntriesComputes (k : ℕ) (hk : 0<k) (label : ℕ) :
    Computes Records.variableEncoding Frame.wordEncoding (fun x=>
      Compiler.entries RawClosedNetwork.vertexEncoding
        ((List.finRange (mainCount k x)).map (fun t=>
          (label,List.ofFn (fun j : Fin k=>mainEndpoint k (mainCount k x)
            (outerOffsetRaw x.1 x.2.val) (innerOffsetRaw k x.1 x.2.val) t.val j.val))) ++
        (List.finRange (connectorCount k x)).flatMap (fun t=>
          [(label,List.ofFn (fun j : Fin k=>firstConnectorEndpoint k
            (outerOffsetRaw x.1 x.2.val) (innerOffsetRaw k x.1 x.2.val) t.val j.val)),
           (label,List.ofFn (fun j : Fin k=>secondConnectorEndpoint k
            (innerOffsetRaw k x.1 x.2.val) t.val j.val))]))) := by
  let main := Indexed.flatMap Records.variableEncoding (mainCount k)
    (Counts.variableMultiplicityComputes k hk) _
    ((mainRowComputes k hk label).andThen (Compiler.entryComputes RawClosedNetwork.vertexEncoding))
  let connectorCountProgram : Computes Records.variableEncoding UnaryBinary.unaryEncoding (connectorCount k) :=
    (Counts.variableMultiplicityComputes k hk).andThen
      UniversalPairReduction.SmoothingCompiler.Endpoints.unaryPredecessorComputes
  let connector := Indexed.flatMap Records.variableEncoding (connectorCount k) connectorCountProgram _
    (Compiler.joinComputes
      ((firstConnectorRowComputes k hk label).andThen (Compiler.entryComputes RawClosedNetwork.vertexEncoding))
      ((secondConnectorRowComputes k hk label).andThen (Compiler.entryComputes RawClosedNetwork.vertexEncoding)))
  exact congrComputes (Compiler.joinComputes main connector) (fun x=>by
    simp only [Function.comp_def,id_eq,Compiler.entries,List.flatMap_append,List.flatMap_map,
      List.flatMap_assoc,List.flatMap_cons,List.flatMap_nil,List.append_nil])

def zeroEntriesComputes (k : ℕ) (hk : 0<k) (label : ℕ) :
    Computes Records.variableEncoding Frame.wordEncoding (fun x=>
      Compiler.entries RawClosedNetwork.vertexEncoding
        [(label,List.ofFn (fun j : Fin k=>(innerOffsetRaw k x.1 x.2.val+j.val,false))),
         (label,List.ofFn (fun j : Fin k=>(innerOffsetRaw k x.1 x.2.val+j.val,true)))]) :=
  congrComputes (Compiler.joinComputes
    ((zeroRowComputes k hk label false).andThen (Compiler.entryComputes RawClosedNetwork.vertexEncoding))
    ((zeroRowComputes k hk label true).andThen (Compiler.entryComputes RawClosedNetwork.vertexEncoding)))
    (fun x=>by simp only [Function.comp_def,Compiler.entries,List.flatMap_cons,List.flatMap_nil,List.append_nil])

def variableEntriesComputes (k : ℕ) (hk : 0<k) (label : ℕ) :
    Computes Records.variableEncoding Frame.wordEncoding (fun x=>
      Compiler.entries RawClosedNetwork.vertexEncoding (variableRowsRaw k label x.1 x.2)) := by
  let zero := Arithmetic.equal (Counts.variableDegreeComputes.andThen UnaryBinary.computes)
    (constantComputes Records.variableEncoding encodingNatBool 0)
  exact congrComputes (Arithmetic.choose Frame.wordEncoding _ _ _ zero
    (zeroEntriesComputes k hk label) (positiveEntriesComputes k hk label))
    (fun x=>by simp only [Function.comp_def,id_eq,variableRowsRaw,macroRows,decide_eq_true_eq,
      mainCount,connectorCount]; split_ifs <;> rfl)

def extraEntriesComputes (k : ℕ) (hk : 0<k) (label : ℕ) :
    Computes Raw.encoding Frame.wordEncoding (fun r=>
      Compiler.entries RawClosedNetwork.vertexEncoding (extraVerticesRaw k label r)) :=
  congrComputes (Records.variablesFlatMap _ (variableEntriesComputes k hk label)) (fun r=>by
    simp only [Function.comp_def,id_eq,extraVerticesRaw,Compiler.entries,List.flatMap_assoc])

end
end Paper2.DegreeCSP.ComputationRecords.Emit
