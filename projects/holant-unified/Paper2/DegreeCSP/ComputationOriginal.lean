import Paper2.DegreeCSP.ComputationOrdinal
import Paper2.DegreeCSP.ComputationCounts

/-! Original ordered constraint records are emitted by actual framed-list scans.
The output keeps every stored scope occurrence in its original port order. -/
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

def endpointComputes {C : Type} {ec : Encoding C Bool} {e : C → ℕ} {b : C → Bool}
    (u : Computes ec encodingNatBool e) (v : Computes ec encodingBoolBool b) :
    Computes ec RawClosedNetwork.endpointEncoding (fun x=>(e x,b x)) :=
  recode (pairComputes u v) id (fun _=>rfl) (fun _=>rfl)

def fixedRowComputes {C : Type} (ec : Encoding C Bool) (k label : ℕ)
    (p : C → Fin k → RawEndpoint)
    (u : ∀j,Computes ec RawClosedNetwork.endpointEncoding (fun x=>p x j)) :
    Computes ec RawClosedNetwork.vertexEncoding (fun x=>(label,List.ofFn (p x))) := by
  let ports := Compiler.fixedListComputes ec RawClosedNetwork.endpointEncoding p u (List.finRange k)
  exact recode (pairComputes (constantComputes ec encodingNatBool label)
    (congrComputes ports (fun x=>List.ofFn_eq_map.symm))) id (fun _=>rfl) (fun _=>rfl)

def originalEndpointComputes : Computes Ports.encoding RawClosedNetwork.endpointEncoding
    (fun p=>originalEndpointRaw p.1.1 (Ports.rawPort p)) := by
  let ordinal := Ordinal.computes.andThen UnaryBinary.computes
  let offset := (Ports.variableContextComputes.andThen Counts.outerOffsetComputes).andThen UnaryBinary.computes
  exact congrComputes (endpointComputes (Arithmetic.add offset ordinal)
    (constantComputes _ encodingBoolBool false)) (fun p=>rfl)

def originalRowComputes : Computes Records.rowEncoding RawClosedNetwork.vertexEncoding
    (fun x=>originalRowRaw x.1 x.2) := by
  let ports := Indexed.flatMap Records.rowEncoding _ Ports.rowPortCountComputes _
    (originalEndpointComputes.andThen (Compiler.entryComputes RawClosedNetwork.endpointEncoding))
  let portList : Computes Records.rowEncoding (framedListEncoding RawClosedNetwork.endpointEncoding)
      (fun x=>List.ofFn (fun j=>originalEndpointRaw x.1 ⟨x.2,j⟩)) :=
    recode (Compiler.joinComputes ports (constantComputes _ Frame.wordEncoding [false])) id
      (fun _=>rfl) (fun x=>by
        change (List.finRange _).flatMap (fun j=>Compiler.entry RawClosedNetwork.endpointEncoding
          (originalEndpointRaw x.1 ⟨x.2,j⟩)) ++ [false]=_
        have h := Compiler.entries_append_encode RawClosedNetwork.endpointEncoding
          ((List.finRange (x.1.factors.get x.2).2.length).map
            (fun j=>originalEndpointRaw x.1 ⟨x.2,j⟩)) []
        simpa only [Compiler.entries,List.ofFn_eq_map,List.flatMap_map,Function.comp_def,List.append_nil,
          framedListEncoding,framedListEncode] using h)
  let label := Records.rowComputes.andThen
    (Wiring.firstComputes encodingNatBool (framedListEncoding encodingNatBool))
  exact recode (pairComputes label portList) id (fun _=>rfl) (fun _=>rfl)

def originalEntriesComputes : Computes Raw.encoding Frame.wordEncoding
    (fun r=>Compiler.entries RawClosedNetwork.vertexEncoding (originalVerticesRaw r)) :=
  congrComputes (Records.rowsFlatMap _ (originalRowComputes.andThen
    (Compiler.entryComputes RawClosedNetwork.vertexEncoding))) (fun r=>by
      simp only [Function.comp_def,id_eq,originalVerticesRaw,Compiler.entries,List.flatMap_map,Function.comp_def])

end
end Paper2.DegreeCSP.ComputationRecords.Emit
