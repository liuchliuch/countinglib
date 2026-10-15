import Paper2.ExactInput.Recognition.NativeKForward
import Holant.Proofs.Recognition.RuntimeTensorRequest
import Holant.Proofs.Algorithms.TransformRecognition.OriginalCatalogueSource

/-! One runtime rational request compares a proposed flattened coefficient
catalogue with the forward source K transform. Source descriptors (including
the fixed edge and numerical constants) are retained before target descriptors. -/
namespace Paper2.ExactInput.Recognition.NativeKSystem
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.RemoteWork.TractChainV1
open CommonFieldMachine (Executes)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev Input := OriginalFamilyPackingMachine.Input × List RootCode
abbrev inputEncoding := pairEncoding OriginalFamilyPackingMachine.encoding CommonFieldMachine.rootsEncoding
abbrev Key := OriginalCatalogueMachine.Key
abbrev keyEncoding := OriginalCatalogueMachine.keyEncoding
abbrev keysEncoding := OriginalCatalogueMachine.keysEncoding
abbrev Cell := Input × Key
abbrev cellEncoding := pairEncoding inputEncoding keyEncoding

def source (r : Input) : OriginalFamilyPackingMachine.Input := (r.1.1,false)
def sourceRoots (r : Input) := OriginalFamilyPackingMachine.roots (source r)
def roots (r : Input) := sourceRoots r ++ r.2
def width (r : Input) := 5+(roots r).length
def imaginary (r : Input) := 5+(OriginalFamilyPackingMachine.original (source r)).length
def sqrt (r : Input) := imaginary r+1
def layout (r : Input) : RuntimeTensorBasis.Layout := (width r,imaginary r,sqrt r)
def keys (r : Input) : List Key := (List.range (source r).1.length).flatMap
  (OriginalCatalogueMachine.atVertex (source r).1)
def sourceAddress (r : Cell) := OriginalCatalogueMachine.address
  (0,OriginalCatalogueMachine.catalogue (source r.1).1,r.2)
def targetAddress (r : Cell) := (sourceRoots r.1).length+sourceAddress r

def equation (r : Cell) : RationalSparseMachine.Poly :=
  NativeKForward.vertex (layout r.1,r.2.2,
    OriginalAddressTablesMachine.table ((source r.1).1,0,r.2.1)) ++
  RationalSparseMachine.neg (RationalSparseMachine.variable (width r.1) (targetAddress r))
def body (r : Input) : RationalInputMachine.Body :=
  RuntimeTensorBasis.rows ((false,false),layout r) ++ (keys r).map (fun k => equation (r,k))
def addresses (r : Input) := (List.range (roots r).length).map (fun j => 5+j)
def request (r : Input) : RationalInputMachine.Input :=
  ⟨width r,roots r,body r,addresses r⟩

 def rawComputes := Wiring.firstComputes OriginalFamilyPackingMachine.encoding CommonFieldMachine.rootsEncoding
 def targetComputes := Wiring.secondComputes OriginalFamilyPackingMachine.encoding CommonFieldMachine.rootsEncoding
 def sourceComputes : Computes inputEncoding OriginalFamilyPackingMachine.encoding source :=
  pairComputes (rawComputes.andThen OriginalFamilyPackingMachine.family)
    (constantComputes inputEncoding encodingBoolBool false)
 def familyComputes := sourceComputes.andThen OriginalFamilyPackingMachine.family
 def sourceRootsComputes := sourceComputes.andThen OriginalFamilyPackingMachine.rootsComputes
 def rootsComputes : Computes inputEncoding CommonFieldMachine.rootsEncoding roots :=
  (pairComputes sourceRootsComputes targetComputes).andThen (WireLists.append ComplexIsolation.CertificateMachine.rootEncoding)
 def rootCountComputes := (rootsComputes.andThen
  (WireLists.lengthComputes ComplexIsolation.CertificateMachine.rootEncoding)).andThen UnaryBinary.computes
 def sourceRootCountComputes := (sourceRootsComputes.andThen
  (WireLists.lengthComputes ComplexIsolation.CertificateMachine.rootEncoding)).andThen UnaryBinary.computes
 def widthComputes : Computes inputEncoding encodingNatBool width :=
  (pairComputes (constantComputes inputEncoding encodingNatBool 5) rootCountComputes).andThen
    RationalInputMachine.Programs.add
 def imaginaryComputes : Computes inputEncoding encodingNatBool imaginary :=
  (pairComputes (constantComputes inputEncoding encodingNatBool 5)
    (sourceComputes.andThen OriginalFamilyPackingMachine.originalsCount)).andThen RationalInputMachine.Programs.add
 def sqrtComputes : Computes inputEncoding encodingNatBool sqrt :=
  imaginaryComputes.andThen RationalInputMachine.Programs.successor
 def layoutComputes : Computes inputEncoding RuntimeTensorBasis.layoutEncoding layout :=
  pairComputes widthComputes (pairComputes imaginaryComputes sqrtComputes)
 def keysExecutes : Executes inputEncoding keysEncoding keys := by
  let count := (familyComputes.andThen (WireLists.lengthComputes OriginalFamilyPackingMachine.vertexEncoding)).andThen UnaryBinary.computes
  let p := Wiring.firstComputes inputEncoding encodingNatBool
  let j := Wiring.secondComputes inputEncoding encodingNatBool
  let cell := (Executes.ofComputes (pairComputes (p.andThen familyComputes) j)).comp OriginalCatalogueMachine.vertexExecutes
  let list := NegativeCertificateMachine.Lists.map inputEncoding encodingNatBool keysEncoding
    ((Executes.ofComputes count).comp RationalInputMachine.Programs.range)
    (fun r j => OriginalCatalogueMachine.atVertex (source r).1 j) cell
  exact (list.comp (Executes.ofComputes (WireLists.flatten keyEncoding))).congr
    (fun r => by simp only [keys,List.flatMap_def,Function.comp_apply,id_eq])

 def cellInputComputes := Wiring.firstComputes inputEncoding keyEncoding
 def cellKeyComputes := Wiring.secondComputes inputEncoding keyEncoding
 def sourceAddressExecutes : Executes cellEncoding encodingNatBool sourceAddress := by
  let catalog := (Executes.ofComputes (cellInputComputes.andThen familyComputes)).comp OriginalCatalogueMachine.executes
  exact ((Executes.ofComputes (constantComputes cellEncoding encodingNatBool 0)).pair
    (catalog.pair (Executes.ofComputes cellKeyComputes))).comp (Executes.ofComputes OriginalCatalogueMachine.addressComputes)
 def targetAddressExecutes : Executes cellEncoding encodingNatBool targetAddress :=
  ((Executes.ofComputes (cellInputComputes.andThen sourceRootCountComputes)).pair sourceAddressExecutes).comp
    (Executes.ofComputes RationalInputMachine.Programs.add)
 def equationExecutes : Executes cellEncoding RationalSparseMachine.encoding equation := by
  let l := cellInputComputes.andThen layoutComputes
  let word := cellKeyComputes.andThen (Wiring.secondComputes encodingNatBool RationalTensorMachine.wordEncoding)
  let j := cellKeyComputes.andThen (Wiring.firstComputes encodingNatBool RationalTensorMachine.wordEncoding)
  let tin := pairComputes (cellInputComputes.andThen familyComputes)
    (pairComputes (constantComputes cellEncoding encodingNatBool 0) j)
  let table := (Executes.ofComputes tin).comp OriginalAddressTablesMachine.executes
  let forward := ((Executes.ofComputes l).pair ((Executes.ofComputes word).pair table)).comp NativeKForward.executes
  let target := ((Executes.ofComputes (cellInputComputes.andThen widthComputes)).pair targetAddressExecutes).comp
    RationalSparseMachine.variableExecutes
  exact (forward.pair (target.comp (Executes.ofComputes RationalSparseMachine.negComputes))).comp
    (Executes.ofComputes (WireLists.append RationalSparseMachine.termEncoding))
 def bodyExecutes : Executes inputEncoding RationalInputMachine.bodyEncoding body := by
  let basis := ((Executes.ofComputes (constantComputes inputEncoding (pairEncoding encodingBoolBool encodingBoolBool) (false,false))).pair
    (Executes.ofComputes layoutComputes)).comp RuntimeTensorBasis.executes
  let rows := NegativeCertificateMachine.Lists.map inputEncoding keyEncoding RationalSparseMachine.encoding
    keysExecutes (fun r k => equation (r,k)) equationExecutes
  exact (basis.pair rows).comp (Executes.ofComputes (WireLists.append RationalSparseMachine.encoding))
 def addressCell : Executes (pairEncoding inputEncoding encodingNatBool) encodingNatBool
    (fun p : Input × ℕ => 5+p.2) :=
  Executes.ofComputes ((pairComputes (constantComputes (pairEncoding inputEncoding encodingNatBool) encodingNatBool 5)
    (Wiring.secondComputes inputEncoding encodingNatBool)).andThen RationalInputMachine.Programs.add)
 def addressesExecutes : Executes inputEncoding RationalInputMachine.addressesEncoding addresses :=
  NegativeCertificateMachine.Lists.map inputEncoding encodingNatBool encodingNatBool
    ((Executes.ofComputes rootCountComputes).comp RationalInputMachine.Programs.range)
    (fun _ j => 5+j) addressCell
 def requestExecutes : Executes inputEncoding RationalInputMachine.encoding request := by
  let raw := (Executes.ofComputes widthComputes).pair
    ((Executes.ofComputes rootsComputes).pair (bodyExecutes.pair addressesExecutes))
  exact Executes.recode raw id (fun _ => rfl) (fun _ => rfl)
 def machine : BinaryCompose.Machine := requestExecutes.machine.compose WitnessOutput.originalMachine

end
end Paper2.ExactInput.Recognition.NativeKSystem
