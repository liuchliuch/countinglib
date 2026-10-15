import Paper2.SourceFaithful.SourceStatements.AlgebraicWitness
import Holant.Proofs.Algorithms.TransformRecognition.RawAffineRecognitionSource
import Holant.Proofs.Algorithms.TransformRecognition.RawProductRecognitionSource
import Holant.Proofs.Algorithms.TransformRecognition.RawLocalAffineRecognitionSource
import Holant.Proofs.AlgebraicRecognition.WitnessOutput.Original
import Holant.Proofs.Recognition.PhysicalFolds

/-! Varying-layout rational request programs for an arbitrary algebraic edge.
All four supplied edge RootCodes survive literally in the original descriptor
list. The A/P/L body builders enumerate their finite normal-form branches and
keep every original coefficient as a separately bound source variable. -/
namespace Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessRuntime
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)
open AlgebraicWitness (Class)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev Input := OriginalFamilyPackingMachine.Input × List RootCode
abbrev encoding := pairEncoding OriginalFamilyPackingMachine.encoding CommonFieldMachine.rootsEncoding

def roots (r : Input) : List RootCode :=
  r.1.1.flatMap Prod.snd ++ r.2 ++ [StandardRootCodes.imaginary, StandardRootCodes.positiveSqrtTwo]

def width (C : Class) (r : Input) : ℕ :=
  match C with
  | .affine => OriginalFamilyPackingMachine.width r.1
  | .product => OriginalAllocatedPackingMachine.width (RawProductRecognitionMachine.allocated r.1)
  | .localAffine => OriginalAllocatedPackingMachine.width (RawLocalAffineRecognitionMachine.allocated r.1)

def body (C : Class) (r : Input) : RationalInputMachine.Body :=
  match C with
  | .affine => RawAffineRecognitionMachine.body r.1
  | .product => RawProductRecognitionMachine.body r.1
  | .localAffine => RawLocalAffineRecognitionMachine.body r.1

def addresses (C : Class) (r : Input) : List ℕ :=
  match C with
  | .affine => OriginalFamilyPackingMachine.addresses r.1
  | .product => OriginalAllocatedPackingMachine.addresses (RawProductRecognitionMachine.allocated r.1)
  | .localAffine => OriginalAllocatedPackingMachine.addresses (RawLocalAffineRecognitionMachine.allocated r.1)

def request (C : Class) (r : Input) : RationalInputMachine.Input :=
  ⟨width C r, roots r, body C r, addresses C r⟩

def sourceComputes := Wiring.firstComputes OriginalFamilyPackingMachine.encoding CommonFieldMachine.rootsEncoding
def edgeComputes := Wiring.secondComputes OriginalFamilyPackingMachine.encoding CommonFieldMachine.rootsEncoding

def rootsComputes : Computes encoding CommonFieldMachine.rootsEncoding roots := by
  let original := sourceComputes.andThen OriginalFamilyPackingMachine.family |>.andThen
    OriginalFamilyPackingMachine.vertexRoots
  let joined := (pairComputes original edgeComputes).andThen
    (WireLists.append ComplexIsolation.CertificateMachine.rootEncoding)
  exact (pairComputes joined (constantComputes encoding CommonFieldMachine.rootsEncoding
    [StandardRootCodes.imaginary, StandardRootCodes.positiveSqrtTwo])).andThen
      (WireLists.append ComplexIsolation.CertificateMachine.rootEncoding)

def widthExecutes (C : Class) : Executes encoding encodingNatBool (width C) := by
  cases C with
  | affine => exact Executes.ofComputes (sourceComputes.andThen OriginalFamilyPackingMachine.widthComputes)
  | product =>
    exact (Executes.ofComputes sourceComputes).comp
      (RawProductRecognitionMachine.allocation.comp (Executes.ofComputes OriginalAllocatedPackingMachine.widthComputes))
  | localAffine =>
    exact (Executes.ofComputes sourceComputes).comp
      (RawLocalAffineRecognitionMachine.allocation.comp (Executes.ofComputes OriginalAllocatedPackingMachine.widthComputes))

def bodyExecutes (C : Class) : Executes encoding RationalSparseMachine.familyEncoding (body C) := by
  cases C with
  | affine => exact (Executes.ofComputes sourceComputes).comp RawAffineRecognitionMachine.bodyExecutes
  | product => exact (Executes.ofComputes sourceComputes).comp RawProductRecognitionMachine.bodyExecutes
  | localAffine => exact (Executes.ofComputes sourceComputes).comp RawLocalAffineRecognitionMachine.bodyExecutes

def addressesExecutes (C : Class) : Executes encoding RationalInputMachine.addressesEncoding (addresses C) := by
  cases C with
  | affine => exact (Executes.ofComputes sourceComputes).comp OriginalFamilyPackingMachine.addressesExecutes
  | product =>
    exact (Executes.ofComputes sourceComputes).comp
      (RawProductRecognitionMachine.allocation.comp OriginalAllocatedPackingMachine.addressesExecutes)
  | localAffine =>
    exact (Executes.ofComputes sourceComputes).comp
      (RawLocalAffineRecognitionMachine.allocation.comp OriginalAllocatedPackingMachine.addressesExecutes)

/-- Each class has one fixed finite controller across all family counts and
arities. Input fields carry only source descriptors, including the four edge
descriptors; no transform, finite branch index or stopping height is input. -/
def requestExecutes (C : Class) : Executes encoding RationalInputMachine.encoding (request C) :=
  Executes.recode ((widthExecutes C).pair ((Executes.ofComputes rootsComputes).pair
    ((bodyExecutes C).pair (addressesExecutes C)))) id (fun _ => rfl) (fun _ => rfl)

def machine (C : Class) : Machine := (requestExecutes C).machine.compose WitnessOutput.originalMachine

end
end Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessRuntime
