import Paper2.DegreeCSP.ComputationLayout
import Holant.Proofs.Tetrahedral.EvenCSPReduction.Program

/-! Actual uniform scans of the total CSP payload. The finite scan, list
selector, indexed traversal and arithmetic programs are the proved Paper 1
programs. These drivers use the raw record itself, so they impose no even-degree
promise and can subsequently be restricted to the degree-k validated encoding. -/
namespace Paper2.DegreeCSP.ComputationRecords
open Holant Holant.Algebraic Holant.Complexity Computability
open Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.Complexity.GraphPreprocessing Holant.Complexity.GraphPreprocessing.OriginalCoefficient
open Holant.Complexity.FixedGadgetSubstitution Holant.OneHot.StackProgram.GraphLabelEncoding
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Program
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
abbrev Factor := ℕ × List ℕ
namespace Records
abbrev inputEncoding := Raw.encoding
abbrev Row := Σr : Raw,Fin r.factors.length
abbrev rowEncoding := sigmaEncoding (inputEncoding)
  (fun r => OccurrenceLabel.unaryPortEncoding r.factors.length)
abbrev Variable := Σr : Raw,Fin r.variables
abbrev variableEncoding := sigmaEncoding (inputEncoding)
  (fun r => OccurrenceLabel.unaryPortEncoding r.variables)

def variablesComputes : Computes (inputEncoding) UnaryBinary.unaryEncoding
    (fun r => r.variables) :=
  recode (Wiring.firstComputes UnaryBinary.unaryEncoding (framedListEncoding Raw.factorEncoding))
    (fun r => (r.variables,r.factors)) (fun _ => rfl) (fun _ => rfl)
def factorsComputes : Computes (inputEncoding) (framedListEncoding Raw.factorEncoding)
    (fun r => r.factors) :=
  recode (Wiring.secondComputes UnaryBinary.unaryEncoding (framedListEncoding Raw.factorEncoding))
    (fun r => (r.variables,r.factors)) (fun _ => rfl) (fun _ => rfl)
def rowsCountComputes : Computes (inputEncoding) UnaryBinary.unaryEncoding
    (fun r => r.factors.length) :=
  (factorsComputes).andThen (Scan.lengthComputes Raw.factorEncoding)

def rowSourceComputes : Computes (rowEncoding) (inputEncoding) (fun x => x.1) :=
  recode (Wiring.firstComputes (inputEncoding) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
def rowIndexComputes : Computes (rowEncoding) UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes (inputEncoding) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
def variableSourceComputes : Computes (variableEncoding) (inputEncoding) (fun x => x.1) :=
  recode (Wiring.firstComputes (inputEncoding) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)
def variableIndexComputes : Computes (variableEncoding) UnaryBinary.unaryEncoding (fun x => x.2.val) :=
  recode (Wiring.secondComputes (inputEncoding) UnaryBinary.unaryEncoding)
    (fun x => (x.1,x.2.val)) (fun _ => rfl) (fun _ => rfl)

def rowComputes : Computes (rowEncoding) Raw.factorEncoding
    (fun x => x.1.factors.get x.2) := by
  let prepare : Computes (rowEncoding) (ParentRowSelect.inputEncoding Raw.factorEncoding)
      (fun x => ⟨x.1.factors,x.2⟩) :=
    recode (pairComputes ((rowSourceComputes).andThen (factorsComputes))
      (rowIndexComputes)) id (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen (ParentRowSelect.computes Raw.factorEncoding)

def rowsComputes : Computes (inputEncoding)
    (ContextFlatMap.inputEncoding (inputEncoding)
      (fun r => OccurrenceLabel.unaryPortEncoding r.factors.length))
    (fun r => ⟨r,List.finRange r.factors.length⟩) :=
  recode (pairComputes (identityComputes (inputEncoding))
    ((rowsCountComputes).andThen ComponentSelection.UnaryRange.computes)) id
    (fun _ => rfl) (fun r => by
      change frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _)=_
      rw [←Compiler.finRange_values,Compiler.finListEncoding]
      rfl)

def variableListComputes : Computes (inputEncoding)
    (ContextFlatMap.inputEncoding (inputEncoding)
      (fun r => OccurrenceLabel.unaryPortEncoding r.variables))
    (fun r => ⟨r,List.finRange r.variables⟩) :=
  recode (pairComputes (identityComputes (inputEncoding))
    ((variablesComputes).andThen ComponentSelection.UnaryRange.computes)) id
    (fun _ => rfl) (fun r => by
      change frame _ ++ framedListEncode UnaryBinary.unaryEncoding (List.range _)=_
      rw [←Compiler.finRange_values,Compiler.finListEncoding]
      rfl)

def rowsFlatMap (f : Row → List Bool)
    (w : Computes (rowEncoding) Frame.wordEncoding f) :
    Computes (inputEncoding) Frame.wordEncoding
      (fun r => (List.finRange r.factors.length).flatMap (fun i => f ⟨r,i⟩)) :=
  (rowsComputes).andThen (ContextFlatMap.computes (inputEncoding)
    (fun r => OccurrenceLabel.unaryPortEncoding r.factors.length) f w)

def variablesFlatMap (f : Variable → List Bool)
    (w : Computes (variableEncoding) Frame.wordEncoding f) :
    Computes (inputEncoding) Frame.wordEncoding
      (fun r => (List.finRange r.variables).flatMap (fun i => f ⟨r,i⟩)) :=
  (variableListComputes).andThen (ContextFlatMap.computes (inputEncoding)
    (fun r => OccurrenceLabel.unaryPortEncoding r.variables) f w)
end Records

namespace Counts
abbrev Context := Raw × ℕ
abbrev encoding := pairEncoding (Raw.encoding) encodingNatBool
def sourceComputes : Computes (encoding) (Raw.encoding) Prod.fst :=
  Wiring.firstComputes _ _
def addressComputes : Computes (encoding) encodingNatBool Prod.snd :=
  Wiring.secondComputes _ _

def rowDegree (x : ℕ × Factor) := (x.2.2.filter (fun j => j==x.1)).length
def rowDegreeComputes : Computes (pairEncoding encodingNatBool Raw.factorEncoding)
    UnaryBinary.unaryEncoding rowDegree := by
  let context := Wiring.firstComputes encodingNatBool Raw.factorEncoding
  let ports := (Wiring.secondComputes encodingNatBool Raw.factorEncoding).andThen
    (Wiring.secondComputes encodingNatBool (framedListEncoding encodingNatBool))
  let prepare : Computes (pairEncoding encodingNatBool Raw.factorEncoding)
      (Scan.encoding encodingNatBool encodingNatBool)
      (fun x => ⟨x.1,x.2.2⟩) :=
    recode (pairComputes context ports) id (fun _ => rfl) (fun _ => rfl)
  exact congrComputes (prepare.andThen (Scan.countComputes encodingNatBool encodingNatBool
    (fun x => decide (x.2=x.1))
    (congrComputes UniversalPairReduction.SmoothingCompiler.Endpoints.equalComputes
      (fun x => by simp only [Function.comp_def,id_eq,eq_comm])))) (fun x => by
    change ((x.2.2.map (fun j => if decide (j=x.1) then 1 else 0)).sum)=
      (x.2.2.filter (fun j => j==x.1)).length
    induction x.2.2 with
    | nil => rfl
    | cons j js ih =>
        simp only [decide_eq_true_eq] at ih
        by_cases h : j=x.1 <;> simp [h,ih,Nat.add_comm])

def degreeComputes : Computes (encoding) UnaryBinary.unaryEncoding
    (fun x => x.1.degree x.2) := by
  let row : Computes (Scan.itemEncoding encodingNatBool Raw.factorEncoding)
      Frame.wordEncoding (fun x => List.replicate (rowDegree (x.1,x.2)) true) :=
    recode (rowDegreeComputes.andThen (Compiler.encodeComputes UnaryBinary.unaryEncoding))
      (fun x => (x.1,x.2)) (fun _ => rfl) (fun _ => rfl)
  let run := Scan.fromComputes encodingNatBool Raw.factorEncoding (encoding)
    Prod.snd (fun x => x.1.factors) (addressComputes)
    ((sourceComputes).andThen (Records.factorsComputes)) _ row
  refine recode run id (fun _ => rfl) (fun x => ?_)
  change x.1.factors.flatMap (fun row => List.replicate (rowDegree (x.2,row)) true)=
    List.replicate (x.1.degree x.2) true
  rw [Scan.tokens]
  apply congrArg (fun n => List.replicate n true)
  symm
  unfold Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.degree
    Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.occurrences
    Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.portList
    Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction.Raw.address
  rw [List.filter_flatMap,List.length_flatMap]
  have inner (v : Fin x.1.factors.length) :
      (((List.finRange (x.1.factors.get v).2.length).map
        (fun j => (⟨v,j⟩ : x.1.Ports))).filter
        (fun p => (x.1.factors.get p.1).2.get p.2==x.2)).length=
        rowDegree (x.2,x.1.factors.get v) := by
    rw [List.filter_map,List.length_map]
    change ((List.finRange _).filter (fun j => (x.1.factors.get v).2.get j==x.2)).length=
      ((x.1.factors.get v).2.filter (fun j => j==x.2)).length
    conv_rhs => rw [←List.map_get_finRange (x.1.factors.get v).2,
      List.filter_map,List.length_map]
    rfl
  simp_rw [inner]
  simpa only [List.map_map,Function.comp_def] using
    congrArg (fun rows => (rows.map (fun row => rowDegree (x.2,row))).sum)
      (List.map_get_finRange x.1.factors)

def variableContextComputes : Computes (Records.variableEncoding) (encoding)
    (fun x => (x.1,x.2.val)) :=
  pairComputes (Records.variableSourceComputes)
    ((Records.variableIndexComputes).andThen UnaryBinary.computes)
def variableDegreeComputes : Computes (Records.variableEncoding) UnaryBinary.unaryEncoding
    (fun x => x.1.degree x.2.val) :=
  (variableContextComputes).andThen (degreeComputes)

end Counts

namespace Ports
abbrev Input := Indexed.Input (fun x : Records.Row => (x.1.factors.get x.2).2.length)
abbrev encoding := Indexed.encoding (Records.rowEncoding)
  (fun x : Records.Row => (x.1.factors.get x.2).2.length)
def rowComputes : Computes (encoding) (Records.rowEncoding) (fun p => p.1) :=
  Indexed.context _ _
def indexComputes : Computes (encoding) UnaryBinary.unaryEncoding (fun p => p.2.val) :=
  Indexed.index _ _
def sourceComputes : Computes (encoding) (Raw.encoding) (fun p => p.1.1) :=
  (rowComputes).andThen (Records.rowSourceComputes)
def rowIndexComputes : Computes (encoding) UnaryBinary.unaryEncoding (fun p => p.1.2.val) :=
  (rowComputes).andThen (Records.rowIndexComputes)
def rowPortsComputes : Computes (Records.rowEncoding) (framedListEncoding encodingNatBool)
    (fun x => (x.1.factors.get x.2).2) :=
  (Records.rowComputes).andThen (Wiring.secondComputes encodingNatBool (framedListEncoding encodingNatBool))
def rowPortCountComputes : Computes (Records.rowEncoding) UnaryBinary.unaryEncoding
    (fun x => (x.1.factors.get x.2).2.length) :=
  (rowPortsComputes).andThen (Scan.lengthComputes encodingNatBool)
def addressComputes : Computes (encoding) encodingNatBool
    (fun p => (p.1.1.factors.get p.1.2).2.get p.2) := by
  let prepare : Computes (encoding) (ParentRowSelect.inputEncoding encodingNatBool)
      (fun p => ⟨(p.1.1.factors.get p.1.2).2,p.2⟩) :=
    recode (pairComputes ((rowComputes).andThen (rowPortsComputes))
      (indexComputes)) id (fun _ => rfl) (fun _ => rfl)
  exact prepare.andThen (ParentRowSelect.computes encodingNatBool)
def rawPort (p : Input) : p.1.1.Ports := ⟨p.1.2,p.2⟩
def variableContextComputes : Computes (encoding) (Counts.encoding)
    (fun p => (p.1.1,p.1.1.address (rawPort p))) :=
  pairComputes (sourceComputes) (addressComputes)
def degreeComputes : Computes (encoding) UnaryBinary.unaryEncoding
    (fun p => p.1.1.degree (p.1.1.address (rawPort p))) :=
  (variableContextComputes).andThen (Counts.degreeComputes)
end Ports

namespace Traversal
variable {C : Type} (ec : Encoding C Bool)
variable (source : C → Raw)
abbrev Row := Indexed.Input (fun c => (source c).factors.length)
abbrev rowEncoding := Indexed.encoding ec (fun c => (source c).factors.length)
def selected (x : Row source) : Records.Row := ⟨source x.1,x.2⟩
def selectedComputes (w : Computes ec (Raw.encoding) source) :
    Computes (rowEncoding ec source) (Records.rowEncoding) (selected source) :=
  recode (pairComputes ((Indexed.context ec _).andThen w) (Indexed.index ec _))
    id (fun _ => rfl) (fun _ => rfl)
abbrev Port := Indexed.Input (fun x : Row source => ((source x.1).factors.get x.2).2.length)
abbrev portEncoding := Indexed.encoding (rowEncoding ec source)
  (fun x : Row source => ((source x.1).factors.get x.2).2.length)
def original (p : Port source) : (source p.1.1).Ports := ⟨p.1.2,p.2⟩
def selectedPort (p : Port source) : Ports.Input := ⟨selected source p.1,p.2⟩
def selectedPortComputes (w : Computes ec (Raw.encoding) source) :
    Computes (portEncoding ec source) (Ports.encoding) (selectedPort source) :=
  recode (pairComputes ((Indexed.context (rowEncoding ec source) _).andThen
    (selectedComputes ec source w)) (Indexed.index (rowEncoding ec source) _))
    id (fun _ => rfl) (fun _ => rfl)
def contextComputes : Computes (portEncoding ec source) ec (fun p => p.1.1) :=
  (Indexed.context (rowEncoding ec source) _).andThen (Indexed.context ec _)
def rowIndexComputes : Computes (portEncoding ec source) UnaryBinary.unaryEncoding (fun p => p.1.2.val) :=
  (Indexed.context (rowEncoding ec source) _).andThen (Indexed.index ec _)
def portIndexComputes : Computes (portEncoding ec source) UnaryBinary.unaryEncoding (fun p => p.2.val) :=
  Indexed.index (rowEncoding ec source) _

/-- Two nested bounded physical traversals preserve original row/slot order. -/
def flatMap (w : Computes ec (Raw.encoding) source)
    (f : Port source → List Bool)
    (provider : Computes (portEncoding ec source) Frame.wordEncoding f) :
    Computes ec Frame.wordEncoding (fun c =>
      (List.finRange (source c).factors.length).flatMap (fun v =>
        (List.finRange ((source c).factors.get v).2.length).flatMap
          (fun j => f ⟨⟨c,v⟩,j⟩))) :=
  Indexed.flatMap ec _ (w.andThen (Records.rowsCountComputes)) _
    (Indexed.flatMap (rowEncoding ec source) _
      ((selectedComputes ec source w).andThen (Ports.rowPortCountComputes)) f provider)

/-- Finite histogram computed by the SAME original incidence scan. -/
def count (w : Computes ec (Raw.encoding) source)
    (test : Port source → Bool)
    (wt : Computes (portEncoding ec source) encodingBoolBool test) :
    Computes ec UnaryBinary.unaryEncoding (fun c =>
      ∑v : Fin (source c).factors.length,
        ∑j : Fin ((source c).factors.get v).2.length,
          if test ⟨⟨c,v⟩,j⟩ then 1 else 0) := by
  let provider := Arithmetic.choose Frame.wordEncoding test (fun _ => [true]) (fun _ => []) wt
    (constantComputes (portEncoding ec source) Frame.wordEncoding [true])
    (constantComputes (portEncoding ec source) Frame.wordEncoding [])
  refine recode (flatMap ec source w _ provider) id (fun _ => rfl) (fun c => ?_)
  change (List.finRange _).flatMap (fun v => (List.finRange _).flatMap
    (fun j => if test ⟨⟨c,v⟩,j⟩ then [true] else []))=List.replicate _ true
  have hi (v : Fin (source c).factors.length) :
      (List.finRange ((source c).factors.get v).2.length).flatMap
        (fun j => if test ⟨⟨c,v⟩,j⟩ then [true] else [])=
        List.replicate (∑j,if test ⟨⟨c,v⟩,j⟩ then 1 else 0) true := by
    calc
      _ = (List.finRange _).flatMap (fun j => List.replicate
          (if test ⟨⟨c,v⟩,j⟩ then 1 else 0) true) := by
            congr 1; funext j; cases test ⟨⟨c,v⟩,j⟩ <;> rfl
      _ = _ := by rw [Scan.tokens,←List.ofFn_eq_map,List.sum_ofFn]
  simp_rw [hi]
  rw [Scan.tokens,←List.ofFn_eq_map,List.sum_ofFn]
end Traversal

end
end Paper2.DegreeCSP.ComputationRecords
