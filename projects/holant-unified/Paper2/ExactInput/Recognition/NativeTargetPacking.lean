import Holant.Proofs.Algorithms.TransformRecognition.ProductAllocationMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalFamilyPackingSource

/-! A total physical regrouping of a flat target descriptor tuple into the
ordered dense vertex tables of the source language. The equality edge flag is
literal false; edge entries are not part of the supplied tuple. -/
namespace Paper2.ExactInput.Recognition.NativeTargetPacking
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.Tractability.AffineMachine
open CommonFieldMachine (Executes)

abbrev Root := RootCode
abbrev Vertex := OriginalFamilyPackingMachine.Vertex
abbrev Packed := OriginalFamilyPackingMachine.Input
abbrev Family := List Vertex
abbrev rootsEncoding := CommonFieldMachine.rootsEncoding
abbrev familyEncoding := OriginalFamilyPackingMachine.familyEncoding
abbrev packedEncoding := OriginalFamilyPackingMachine.encoding
abbrev Input := Packed × List Root
abbrev inputEncoding := pairEncoding packedEncoding rootsEncoding
abbrev RowInput := Input × ℕ
abbrev rowInputEncoding := pairEncoding inputEncoding encodingNatBool

def defaultRoot : Root := RationalRootCode.code 0
def entryCount (xs : Family) : ℕ := (xs.flatMap Prod.snd).length
def offset (xs : Family) (i : ℕ) : ℕ :=
  ((List.range i).map (fun j => (xs.getD j (0,[])).2.length)).sum
def block (cs : List Root) (start count : ℕ) : List Root :=
  (List.range count).map (fun j => cs.getD (start+j) defaultRoot)
def row (p : RowInput) : Vertex :=
  ((p.1.1.1.getD p.2 (0,[])).1,
    block p.1.2 (offset p.1.1.1 p.2) (p.1.1.1.getD p.2 (0,[])).2.length)
def family (p : Input) : Family :=
  (List.range p.1.1.length).map (fun i => row (p,i))
def reshape (p : Input) : Packed := (family p,false)

theorem block_length (cs : List Root) (start count : ℕ) :
    (block cs start count).length=count := by simp [block]
theorem family_length (p : Input) : (family p).length=p.1.1.length := by simp [family]
theorem equality_flag (p : Input) : (reshape p).2=false := rfl
theorem row_at (p : Input) (i : ℕ) (hi : i<p.1.1.length) :
    (family p).getD i (0,[])=row (p,i) := by
  simp [family,List.getD_eq_getElem?_getD,hi]
theorem row_arity (p : Input) (i : ℕ) (hi : i<p.1.1.length) :
    ((reshape p).1.getD i (0,[])).1=(p.1.1.getD i (0,[])).1 := by
  rw [reshape,row_at p i hi]; rfl
theorem row_length (p : Input) (i : ℕ) (hi : i<p.1.1.length) :
    ((reshape p).1.getD i (0,[])).2.length=(p.1.1.getD i (0,[])).2.length := by
  rw [reshape,row_at p i hi]; exact block_length ..
theorem row_entry (p : Input) (i j : ℕ) (hi : i<p.1.1.length)
    (hj : j<(p.1.1.getD i (0,[])).2.length) :
    (((reshape p).1.getD i (0,[])).2).getD j defaultRoot =
      p.2.getD (offset p.1.1 i+j) defaultRoot := by
  rw [reshape,row_at p i hi]
  simp only [List.getD_eq_getElem?_getD] at hj
  simp [row,block,List.getD_eq_getElem?_getD,hj]

noncomputable section

def sourceComputes : Computes inputEncoding familyEncoding (fun p : Input => p.1.1) :=
  (Wiring.firstComputes packedEncoding rootsEncoding).andThen
    (Wiring.firstComputes familyEncoding encodingBoolBool)
def targetsComputes : Computes inputEncoding rootsEncoding (fun p : Input => p.2) :=
  Wiring.secondComputes packedEncoding rootsEncoding
def countComputes : Computes inputEncoding encodingNatBool (fun p : Input => p.1.1.length) :=
  (sourceComputes.andThen (WireLists.lengthComputes OriginalFamilyPackingMachine.vertexEncoding)).andThen
    UnaryBinary.computes

abbrev prefixEncoding := pairEncoding familyEncoding encodingNatBool
def prefixCell : Executes (pairEncoding prefixEncoding encodingNatBool) encodingNatBool
    (fun p : (Family × ℕ) × ℕ => (p.1.1.getD p.2 (0,[])).2.length) := by
  let xs := (Wiring.firstComputes prefixEncoding encodingNatBool).andThen
    (Wiring.firstComputes familyEncoding encodingNatBool)
  let j := Wiring.secondComputes prefixEncoding encodingNatBool
  let v := (Executes.ofComputes (pairComputes xs j)).comp
    (NegativeCertificateMachine.Lists.lookup OriginalFamilyPackingMachine.vertexEncoding (0,[]))
  exact v.comp (Executes.ofComputes
    (((Wiring.secondComputes encodingNatBool rootsEncoding).andThen
      (WireLists.lengthComputes ComplexIsolation.CertificateMachine.rootEncoding)).andThen UnaryBinary.computes))
def offsetExecutes : Executes prefixEncoding encodingNatBool (fun p : Family × ℕ => offset p.1 p.2) :=
  (NegativeCertificateMachine.Lists.map prefixEncoding encodingNatBool encodingNatBool
    ((Executes.ofComputes (Wiring.secondComputes familyEncoding encodingNatBool)).comp
      RationalInputMachine.Programs.range)
    (fun p j => (p.1.getD j (0,[])).2.length) prefixCell).comp ProductAllocationMachine.sumExecutes

abbrev blockInputEncoding := pairEncoding rootsEncoding (pairEncoding encodingNatBool encodingNatBool)
def blockCell : Executes (pairEncoding blockInputEncoding encodingNatBool)
    ComplexIsolation.CertificateMachine.rootEncoding
    (fun p : (List Root × (ℕ × ℕ)) × ℕ => p.1.1.getD (p.1.2.1+p.2) defaultRoot) := by
  let ctx := Wiring.firstComputes blockInputEncoding encodingNatBool
  let xs := ctx.andThen (Wiring.firstComputes rootsEncoding (pairEncoding encodingNatBool encodingNatBool))
  let start := ctx.andThen (Wiring.secondComputes rootsEncoding (pairEncoding encodingNatBool encodingNatBool))
    |>.andThen (Wiring.firstComputes encodingNatBool encodingNatBool)
  let j := Wiring.secondComputes blockInputEncoding encodingNatBool
  exact (Executes.ofComputes (pairComputes xs
    ((pairComputes start j).andThen RationalInputMachine.Programs.add))).comp
      (NegativeCertificateMachine.Lists.lookup ComplexIsolation.CertificateMachine.rootEncoding defaultRoot)
def blockExecutes : Executes blockInputEncoding rootsEncoding
    (fun p : List Root × (ℕ × ℕ) => block p.1 p.2.1 p.2.2) :=
  NegativeCertificateMachine.Lists.map blockInputEncoding encodingNatBool
    ComplexIsolation.CertificateMachine.rootEncoding
    ((Executes.ofComputes ((Wiring.secondComputes rootsEncoding (pairEncoding encodingNatBool encodingNatBool)).andThen
      (Wiring.secondComputes encodingNatBool encodingNatBool))).comp RationalInputMachine.Programs.range)
    (fun p j => p.1.getD (p.2.1+j) defaultRoot) blockCell

def rowExecutes : Executes rowInputEncoding OriginalFamilyPackingMachine.vertexEncoding row := by
  let ctx := Wiring.firstComputes inputEncoding encodingNatBool
  let xs := ctx.andThen sourceComputes
  let cs := ctx.andThen targetsComputes
  let i := Wiring.secondComputes inputEncoding encodingNatBool
  let v := (Executes.ofComputes (pairComputes xs i)).comp
    (NegativeCertificateMachine.Lists.lookup OriginalFamilyPackingMachine.vertexEncoding (0,[]))
  let arity := v.comp (Executes.ofComputes (Wiring.firstComputes encodingNatBool rootsEncoding))
  let len := v.comp (Executes.ofComputes
    (((Wiring.secondComputes encodingNatBool rootsEncoding).andThen
      (WireLists.lengthComputes ComplexIsolation.CertificateMachine.rootEncoding)).andThen UnaryBinary.computes))
  let off := (Executes.ofComputes (pairComputes xs i)).comp offsetExecutes
  let entries := ((Executes.ofComputes cs).pair (off.pair len)).comp blockExecutes
  exact arity.pair entries

def familyExecutes : Executes inputEncoding familyEncoding family :=
  NegativeCertificateMachine.Lists.map inputEncoding encodingNatBool
    OriginalFamilyPackingMachine.vertexEncoding
    ((Executes.ofComputes countComputes).comp RationalInputMachine.Programs.range)
    (fun p i => row (p,i)) rowExecutes
def executes : Executes inputEncoding packedEncoding reshape :=
  familyExecutes.pair (Executes.ofComputes (constantComputes inputEncoding encodingBoolBool false))

end
end Paper2.ExactInput.Recognition.NativeTargetPacking
