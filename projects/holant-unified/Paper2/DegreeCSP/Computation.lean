import Paper2.DegreeCSP.ComputationMacroRows
import Paper2.TractableAlgorithms.Paper1Machine

/-! The complete actual degree-k incidence-query byte compiler. Its machine
scans the declared records and variables, emits the deterministic equality
macros, and retains the native-X edge list in the agreed stable order. -/
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

def verticesComputes (k : ℕ) (hk : 0<k) (label : ℕ) :
    Computes Raw.encoding (framedListEncoding RawClosedNetwork.vertexEncoding)
      (verticesRaw k label) :=
  recode (Compiler.joinComputes (Compiler.joinComputes originalEntriesComputes
    (extraEntriesComputes k hk label)) (constantComputes _ Frame.wordEncoding [false])) id
    (fun _=>rfl) (fun r=>by
      change (Compiler.entries RawClosedNetwork.vertexEncoding (originalVerticesRaw r) ++
        Compiler.entries RawClosedNetwork.vertexEncoding (extraVerticesRaw k label r)) ++ [false]=_
      have h : Compiler.entries RawClosedNetwork.vertexEncoding (originalVerticesRaw r) ++
          Compiler.entries RawClosedNetwork.vertexEncoding (extraVerticesRaw k label r)=
          Compiler.entries RawClosedNetwork.vertexEncoding (verticesRaw k label r) := by
        simp only [verticesRaw,Compiler.entries,List.flatMap_append]
      rw [h]
      simpa only [List.append_nil,framedListEncoding,framedListEncode] using
        Compiler.entries_append_encode RawClosedNetwork.vertexEncoding (verticesRaw k label r) [])

def edgesComputes (k : ℕ) (hk : 0<k) :
    Computes Raw.encoding (framedListEncoding encodingNatBool)
      (fun r=>List.replicate (edgeCountRaw k r) 0) := by
  let tokens := Indexed.flatMap Raw.encoding (edgeCountRaw k) (Counts.edgeCountComputes k hk)
    (fun _=>Compiler.entry encodingNatBool 0)
    (constantComputes (Indexed.encoding Raw.encoding (edgeCountRaw k))
      Frame.wordEncoding (Compiler.entry encodingNatBool 0))
  exact recode (Compiler.joinComputes tokens (constantComputes _ Frame.wordEncoding [false])) id
    (fun _=>rfl) (fun r=>by
      change (List.finRange _).flatMap (fun _=>Compiler.entry encodingNatBool 0) ++ [false]=_
      have h : (List.finRange (edgeCountRaw k r)).map (fun _=>(0 : ℕ))=
          List.replicate (edgeCountRaw k r) 0 := by
        simp only [List.map_const',List.length_finRange]
      have he := Compiler.entries_append_encode encodingNatBool
        ((List.finRange (edgeCountRaw k r)).map (fun _=>(0 : ℕ))) []
      rw [←h]
      simpa only [Compiler.entries,List.flatMap_map,Function.comp_def,id_eq,List.append_nil,
        framedListEncoding,framedListEncode] using he)

/-- This receipt contains a concrete finite Boolean-stack machine and its
polynomial transition clock, for all literal raw records. -/
def rawComputes (k : ℕ) (hk : 0<k) (label : ℕ) :
    Computes Raw.encoding RawClosedNetwork.encoding (rawTotal k label) :=
  recode (pairComputes (verticesComputes k hk label) (edgesComputes k hk)) id
    (fun _=>rfl) (fun _=>rfl)

/-- Promise validation changes no input byte or output record. -/
def promisedRawComputes (s : ℕ) (a : ℕ → ℕ) (k : ℕ) (hk : 0<k) (label : ℕ) :
    Computes (Raw.validatedEncoding s a k) RawClosedNetwork.encoding (raw label) :=
  recode (rawComputes k hk label) (fun r=>r.val) (fun _=>rfl)
    (fun r=>congrArg RawClosedNetwork.encoding.encode (rawTotal_eq label r))

end
end Paper2.DegreeCSP.ComputationRecords.Emit

namespace Paper2.DegreeCSP
noncomputable section

def rawQueryComputes (k : ℕ) (hk : 0<k) (label : ℕ) :
    Paper2.Complexity.BinaryCompose.Computes Raw.encoding
      Holant.Complexity.RawClosedNetwork.encoding (ComputationLayout.rawTotal k label) :=
  TractableAlgorithms.Paper1Machine.computes (ComputationRecords.Emit.rawComputes k hk label)

def promisedRawQueryComputes (s : ℕ) (a : ℕ → ℕ) (k : ℕ) (hk : 0<k) (label : ℕ) :
    Paper2.Complexity.BinaryCompose.Computes (Raw.validatedEncoding s a k)
      Holant.Complexity.RawClosedNetwork.encoding (ComputationLayout.raw label) :=
  TractableAlgorithms.Paper1Machine.computes (ComputationRecords.Emit.promisedRawComputes s a k hk label)

end
end Paper2.DegreeCSP
