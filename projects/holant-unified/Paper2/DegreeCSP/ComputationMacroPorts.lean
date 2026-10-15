import Paper2.DegreeCSP.ComputationOriginal

/-! The equality macro's ordered ports have fixed finite branch programs.
Runtime arithmetic only reads a declared variable and its unary block index. -/
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

abbrev Block (count : Records.Variable → ℕ) := Indexed.Input count
abbrev blockEncoding (count : Records.Variable → ℕ) := Indexed.encoding Records.variableEncoding count

def blockContextComputes (count : Records.Variable → ℕ) :
    Computes (blockEncoding count) Records.variableEncoding (fun x=>x.1) := Indexed.context _ _
def blockIndexComputes (count : Records.Variable → ℕ) :
    Computes (blockEncoding count) UnaryBinary.unaryEncoding (fun x=>x.2.val) := Indexed.index _ _

def mainEndpointComputes (count : Records.Variable → ℕ) (k : ℕ) (hk : 0<k) (j : Fin k) :
    Computes (blockEncoding count) RawClosedNetwork.endpointEncoding (fun x=>
      mainEndpoint k (ComputationLayout.multiplicity k (Raw.degree x.1.1 x.1.2.val))
        (outerOffsetRaw x.1.1 x.1.2.val) (innerOffsetRaw k x.1.1 x.1.2.val) x.2.val j.val) := by
  let ec := blockEncoding count
  let context := blockContextComputes count
  let t := (blockIndexComputes count).andThen UnaryBinary.computes
  let m := (context.andThen (Counts.variableMultiplicityComputes k hk)).andThen UnaryBinary.computes
  let outer := (context.andThen Counts.variableOuterOffsetComputes).andThen UnaryBinary.computes
  let inner := (context.andThen (Counts.variableInnerOffsetComputes k hk)).andThen UnaryBinary.computes
  let fixed (n : ℕ) := constantComputes ec encodingNatBool n
  let side (b : Bool) := constantComputes ec encodingBoolBool b
  let tk := Counts.binaryScale t k
  let external := endpointComputes (Arithmetic.add (Arithmetic.add outer tk) (fixed j.val)) (side true)
  by_cases h0 : j.val=0
  · let previous := Counts.binaryScale (Arithmetic.subtract t (fixed 1)) k
    exact congrComputes (Arithmetic.choose RawClosedNetwork.endpointEncoding _ _ _
      (Arithmetic.less (fixed 0) t)
      (endpointComputes (Arithmetic.add (Arithmetic.add inner previous) (fixed 1)) (side false)) external)
      (fun x=>by simp [mainEndpoint,h0,Function.comp_def,decide_eq_true_eq])
  · by_cases h1 : j.val=1
    · exact congrComputes (Arithmetic.choose RawClosedNetwork.endpointEncoding _ _ _
        (Arithmetic.less (Arithmetic.add t (fixed 1)) m)
        (endpointComputes (Arithmetic.add inner tk) (side false)) external)
        (fun x=>by simp [mainEndpoint,h0,h1,Function.comp_def,decide_eq_true_eq])
    · exact congrComputes external (fun x=>by simp [mainEndpoint,h0,h1])

def firstConnectorEndpointComputes (count : Records.Variable → ℕ) (k : ℕ) (hk : 0<k) (j : Fin k) :
    Computes (blockEncoding count) RawClosedNetwork.endpointEncoding (fun x=>
      firstConnectorEndpoint k (outerOffsetRaw x.1.1 x.1.2.val)
        (innerOffsetRaw k x.1.1 x.1.2.val) x.2.val j.val) := by
  let ec := blockEncoding count
  let context := blockContextComputes count
  let t := (blockIndexComputes count).andThen UnaryBinary.computes
  let outer := (context.andThen Counts.variableOuterOffsetComputes).andThen UnaryBinary.computes
  let inner := (context.andThen (Counts.variableInnerOffsetComputes k hk)).andThen UnaryBinary.computes
  let fixed (n : ℕ) := constantComputes ec encodingNatBool n
  let side (b : Bool) := constantComputes ec encodingBoolBool b
  by_cases h0 : j.val=0
  · exact congrComputes (endpointComputes
      (Arithmetic.add (Arithmetic.add outer (Counts.binaryScale t k)) (fixed 1)) (side true))
      (fun x=>by simp [firstConnectorEndpoint,h0])
  · by_cases h1 : j.val=1
    · exact congrComputes (endpointComputes
        (Arithmetic.add outer (Counts.binaryScale (Arithmetic.add t (fixed 1)) k)) (side true))
        (fun x=>by simp [firstConnectorEndpoint,h0,h1])
    · exact congrComputes (endpointComputes
        (Arithmetic.add (Arithmetic.add inner (Counts.binaryScale t k)) (fixed j.val)) (side false))
        (fun x=>by simp [firstConnectorEndpoint,h0,h1])

def secondConnectorEndpointComputes (count : Records.Variable → ℕ) (k : ℕ) (hk : 0<k) (j : Fin k) :
    Computes (blockEncoding count) RawClosedNetwork.endpointEncoding (fun x=>
      secondConnectorEndpoint k (innerOffsetRaw k x.1.1 x.1.2.val) x.2.val j.val) := by
  let t := (blockIndexComputes count).andThen UnaryBinary.computes
  let inner := ((blockContextComputes count).andThen (Counts.variableInnerOffsetComputes k hk)).andThen UnaryBinary.computes
  exact congrComputes (endpointComputes
    (Arithmetic.add (Arithmetic.add inner (Counts.binaryScale t k))
      (constantComputes (blockEncoding count) encodingNatBool j.val))
    (constantComputes (blockEncoding count) encodingBoolBool true)) (fun x=>rfl)

def zeroEndpointComputes (k : ℕ) (hk : 0<k) (b : Bool) (j : Fin k) :
    Computes Records.variableEncoding RawClosedNetwork.endpointEncoding
      (fun x=>(innerOffsetRaw k x.1 x.2.val+j.val,b)) :=
  endpointComputes (Arithmetic.add ((Counts.variableInnerOffsetComputes k hk).andThen UnaryBinary.computes)
    (constantComputes _ encodingNatBool j.val)) (constantComputes _ encodingBoolBool b)

end
end Paper2.DegreeCSP.ComputationRecords.Emit
