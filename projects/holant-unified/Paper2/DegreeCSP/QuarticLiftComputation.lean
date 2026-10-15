import Paper2.DegreeCSP.QuarticLiftLayout
import Paper2.DegreeCSP.ComputationCounts
import Paper2.TractableAlgorithms.Paper1Machine

/-! The actual bounded-stack program expanding every literal lifted-binary
vertex into its fixed partial-CSP presentation. Source rows and edges are
traversed in their original order; every scope address is read or computed by
proved finite programs. -/
namespace Paper2.DegreeCSP.QuarticLiftComputation
open Holant Holant.Algebraic Holant.Complexity Computability
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.Complexity.GraphPreprocessing Holant.Complexity.GraphPreprocessing.OriginalCoefficient
open Holant.Complexity.FixedGadgetSubstitution Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Program
open QuarticLiftLayout
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

def endpointAddressComputes : Computes RawClosedNetwork.endpointEncoding encodingNatBool endpointAddress := by
  let edge := Wiring.firstComputes encodingNatBool encodingBoolBool
  let side := Wiring.secondComputes encodingNatBool encodingBoolBool
  let token := Arithmetic.choose encodingNatBool (fun p : RawEndpoint => p.2)
    (fun _ => 1) (fun _ => 0) side
    (constantComputes _ encodingNatBool 1) (constantComputes _ encodingNatBool 0)
  exact congrComputes (Arithmetic.add (ComputationRecords.Counts.binaryScale edge 2) token)
    (fun p => by simp only [endpointAddress,Nat.mul_comm p.1 2])

def sourcePortComputes (i : ℕ) : Computes vertexEncoding RawClosedNetwork.endpointEncoding
    (fun x => sourcePort x i) :=
  ((Compiler.originalRowComputes 1 1 (fun _ => 4)).andThen
    (Wiring.secondComputes encodingNatBool (framedListEncoding RawClosedNetwork.endpointEncoding))).andThen
      (Compiler.getDComputes RawClosedNetwork.endpointEncoding i (0,false))

def sourceAddressComputes (i : ℕ) : Computes vertexEncoding encodingNatBool
    (fun x => endpointAddress (sourcePort x i)) :=
  (sourcePortComputes i).andThen endpointAddressComputes

def hiddenAddressComputes (P : Presentation Paper2.Tractable.AlgebraicComplex (Fin 2))
    (h : Fin P.hiddenCount) : Computes vertexEncoding encodingNatBool (fun x => hiddenAddress P x h) := by
  let edge := ((Compiler.sourceComputes 1 1 (fun _ => 4)).andThen
    (Compiler.edgeCountComputes 1 1 (fun _ => 4))).andThen UnaryBinary.computes
  let vertex := (Compiler.indexComputes 1 1 (fun _ => 4)).andThen UnaryBinary.computes
  exact congrComputes (Arithmetic.add (Arithmetic.add
    (ComputationRecords.Counts.binaryScale edge 2)
    (ComputationRecords.Counts.binaryScale vertex P.hiddenCount))
    (constantComputes vertexEncoding encodingNatBool h.val))
    (fun x => by simp only [hiddenAddress,Function.comp_def,id_eq,Nat.mul_comm x.1.val.edges.length 2])

def scopeAddressComputes (P : Presentation Paper2.Tractable.AlgebraicComplex (Fin 2))
    (s : Fin 2 ⊕ Fin P.hiddenCount) :
    Computes vertexEncoding encodingNatBool (fun x => scopeAddress P x s) := by
  cases s with
  | inl j => exact sourceAddressComputes (2*j.val)
  | inr h => exact hiddenAddressComputes P h

def oldFactorComputes (P : Presentation Paper2.Tractable.AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (c : Fin P.constraints) :
    Computes vertexEncoding Raw.factorEncoding (fun x => oldFactor P labels x c) := by
  let scope := Compiler.fixedListComputes vertexEncoding encodingNatBool
    (fun x i => scopeAddress P x (P.scope c i))
    (fun i => scopeAddressComputes P (P.scope c i)) (List.finRange (P.arity c))
  exact recode (pairComputes (constantComputes vertexEncoding encodingNatBool (labels c))
    (congrComputes scope (fun x => List.ofFn_eq_map.symm))) id (fun _ => rfl) (fun _ => rfl)

def localFactorComputes (label : ℕ) (j : Fin 2) :
    Computes vertexEncoding Raw.factorEncoding (fun x => localFactor label x j) := by
  let scope := Compiler.fixedListComputes vertexEncoding encodingNatBool
    (fun x (i : Fin 2) => endpointAddress (sourcePort x (2*j.val+i.val)))
    (fun i => sourceAddressComputes (2*j.val+i.val)) [0,1]
  exact recode (pairComputes (constantComputes vertexEncoding encodingNatBool label) scope)
    id (fun _ => rfl) (fun _ => rfl)

def repeatEntriesComputes {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
    (f : A → B) (w : Computes ea eb f) (k : ℕ) :
    Computes ea Frame.wordEncoding (fun x => Compiler.entries eb (List.replicate k (f x))) := by
  exact congrComputes (Compiler.fixedConcatComputes ea
    (fun x (_ : Unit) => Compiler.entry eb (f x))
    (fun _ => w.andThen (Compiler.entryComputes eb)) (List.replicate k ()))
    (fun x => by simp only [Compiler.entries,List.flatMap_replicate])

def vertexEntriesComputes (P : Presentation Paper2.Tractable.AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) :
    Computes vertexEncoding Frame.wordEncoding
      (fun x => Compiler.entries Raw.factorEncoding (vertexFactors P labels k label x)) := by
  let old := Compiler.fixedConcatComputes vertexEncoding
    (fun x c => Compiler.entry Raw.factorEncoding (oldFactor P labels x c))
    (fun c => (oldFactorComputes P labels c).andThen (Compiler.entryComputes Raw.factorEncoding))
    (List.finRange P.constraints)
  let pairs := Compiler.fixedConcatComputes vertexEncoding
    (fun x j => Compiler.entries Raw.factorEncoding (List.replicate k (localFactor label x j)))
    (fun j => repeatEntriesComputes vertexEncoding Raw.factorEncoding _ (localFactorComputes label j) k)
    (List.finRange 2)
  exact congrComputes (Compiler.joinComputes old pairs) (fun x => by
    simp only [vertexFactors,Compiler.entries,List.flatMap_append,List.flatMap_assoc,
      List.ofFn_eq_map,List.flatMap_map,Function.comp_def])

abbrev Edge := Indexed.Input (fun r : Input => r.val.edges.length)
abbrev edgeEncoding := Indexed.encoding inputEncoding (fun r : Input => r.val.edges.length)

def outerFactorComputes (label : ℕ) : Computes edgeEncoding Raw.factorEncoding
    (fun x => outerFactor label x.2.val) := by
  let index := (Indexed.index inputEncoding (fun r : Input => r.val.edges.length)).andThen UnaryBinary.computes
  let base := ComputationRecords.Counts.binaryScale index 2
  let successor := Arithmetic.add base (constantComputes edgeEncoding encodingNatBool 1)
  let scope := Compiler.fixedListComputes edgeEncoding encodingNatBool
    (fun x (b : Bool) => if b then 2*x.2.val+1 else 2*x.2.val)
    (fun b => by
      cases b
      · exact congrComputes base (fun x => by simp [Function.comp_def,Nat.mul_comm])
      · exact congrComputes successor (fun x => by simp [Function.comp_def,Nat.mul_comm])) [false,true]
  exact recode (pairComputes (constantComputes edgeEncoding encodingNatBool label) scope)
    id (fun _ => rfl) (fun _ => rfl)

def factorEntriesComputes (P : Presentation Paper2.Tractable.AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) :
    Computes inputEncoding Frame.wordEncoding
      (fun r => Compiler.entries Raw.factorEncoding (factors P labels k label r)) := by
  let vertices := Compiler.allRowsFlatMapComputes 1 1 (fun _ => 4) _
    (vertexEntriesComputes P labels k label)
  let edges := Indexed.flatMap inputEncoding (fun r : Input => r.val.edges.length)
    (Compiler.edgeCountComputes 1 1 (fun _ => 4)) _
    (repeatEntriesComputes edgeEncoding Raw.factorEncoding _ (outerFactorComputes label) k)
  exact congrComputes (Compiler.joinComputes vertices edges) (fun r => by
    simp only [factors,Compiler.entries,List.flatMap_append,List.flatMap_assoc])

def factorsComputes (P : Presentation Paper2.Tractable.AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) :
    Computes inputEncoding (framedListEncoding Raw.factorEncoding) (factors P labels k label) :=
  recode (Compiler.joinComputes (factorEntriesComputes P labels k label)
    (constantComputes inputEncoding Frame.wordEncoding [false])) id (fun _ => rfl)
    (fun r => by simpa only [List.append_nil,framedListEncoding,framedListEncode,Frame.wordEncoding,Function.comp_def,id_eq] using
      Compiler.entries_append_encode Raw.factorEncoding (factors P labels k label r) [])

def variablesComputes (P : Presentation Paper2.Tractable.AlgebraicComplex (Fin 2)) :
    Computes inputEncoding UnaryBinary.unaryEncoding
      (fun r => 2*r.val.edges.length+r.val.vertices.length*P.hiddenCount) :=
  congrComputes (Arithmetic.unaryAdd
    ((Compiler.edgeCountComputes 1 1 (fun _ => 4)).andThen (ComputationRecords.Counts.unaryScaleComputes 2))
    ((Compiler.vertexCountComputes 1 1 (fun _ => 4)).andThen
      (ComputationRecords.Counts.unaryScaleComputes P.hiddenCount)))
    (fun r => by simp only [Function.comp_def,id_eq,Nat.mul_comm r.val.edges.length 2])

def rawComputes (P : Presentation Paper2.Tractable.AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) :
    Computes inputEncoding Raw.encoding (raw P labels k label) :=
  recode (pairComputes (variablesComputes P) (factorsComputes P labels k label))
    id (fun _ => rfl) (fun _ => rfl)

/-- The finite source machine and clock transfer literally to Paper 2. -/
def computes (P : Presentation Paper2.Tractable.AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) :
    Paper2.Complexity.BinaryCompose.Computes inputEncoding Raw.encoding (raw P labels k label) :=
  Paper2.TractableAlgorithms.Paper1Machine.computes (rawComputes P labels k label)

end
end Paper2.DegreeCSP.QuarticLiftComputation
