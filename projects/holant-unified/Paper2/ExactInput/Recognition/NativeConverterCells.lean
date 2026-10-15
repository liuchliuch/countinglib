import Paper2.ExactInput.Recognition.NativeCertifiedCatalogue
import Paper2.ExactInput.Recognition.NativeKSystemSource
import Paper2.ExactInput.Recognition.NativeTargetData
import Paper2.ExactInput.Recognition.NativeCandidateSelection

/-! Every cell of the native-table search contains a tuple emitted by the
certified root catalogue. Its semantic values certify the actual request;
the physical cell drops the search height, executes the K comparison machine,
and reads the returned option tag. Source coefficient counts are obtained by
scanning and flattening the original vertex tables, without edge entries. -/
namespace Paper2.ExactInput.Recognition.NativeConverterCells
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.LocalDrafts.RemoteWork.TractChainV1
open PhysicalFolds
open CommonFieldMachine (Executes)
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

abbrev Datum := RuntimeSupportTable.Data × ℕ
abbrev Packed := OriginalFamilyPackingMachine.Input
abbrev Root := NativeCertifiedCatalogue.Root
abbrev rootsEncoding := NativeCertifiedCatalogue.rootsEncoding
abbrev contextEncoding := pairEncoding OriginalFamilyPackingMachine.encoding encodingNatBool
abbrev cellEncoding := pairEncoding contextEncoding rootsEncoding

def context (d : Datum) : Packed × ℕ := (RuntimeSupportTable.original d.1,d.2)
def items (d : Datum) : List (List Root) :=
  NativeCertifiedCatalogue.tuples (NativeKSystem.coefficientCount d.1) d.2
abbrev Cell := PromisedListMap.Cell items

def tupleRoot (c : Cell) (j : Fin (NativeKSystem.coefficientCount c.1.1)) : Root :=
  c.2.val.get (Fin.cast (NativeCertifiedCatalogue.tuple_length c.2.property).symm j)

theorem tupleRoot_valid (c : Cell) (j : Fin (NativeKSystem.coefficientCount c.1.1)) :
    ∃ z : AlgebraicComplex, (tupleRoot c j).Represents (z : ℂ) :=
  NativeCertifiedCatalogue.tuple_entries_valid c.2.property _ (List.get_mem ..)

def tupleData (c : Cell) : NativeKSystem.Data where
  source := c.1.1
  target := tupleRoot c
  value j := Classical.choose (tupleRoot_valid c j)
  represented j := Classical.choose_spec (tupleRoot_valid c j)

@[simp] theorem tupleData_source (c : Cell) : (tupleData c).source=c.1.1 := rfl

theorem tupleData_encode (c : Cell) :
    NativeKSystem.encode (tupleData c) = (RuntimeSupportTable.original c.1.1,c.2.val) := by
  apply Prod.ext
  · rfl
  change List.ofFn (tupleRoot c) = c.2.val
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using
      (NativeCertifiedCatalogue.tuple_length c.2.property).symm
  · intro i hi hj
    simp [tupleRoot]

theorem tupleData_target_getD (c : Cell)
    (j : Fin (NativeKSystem.coefficientCount c.1.1)) :
    (tupleData c).target j = c.2.val.getD j.val NativeTargetPacking.defaultRoot := by
  have hj : j.val<c.2.val.length := by
    rw [NativeCertifiedCatalogue.tuple_length c.2.property]
    exact j.isLt
  simp [tupleData,tupleRoot,List.getD_eq_getElem?_getD,hj]

theorem target_atword (c : Cell) (i : Fin c.1.1.count)
    (x : Fin (c.1.1.arity i) → Bool) :
    (tupleData c).target
      ⟨(LocalAffineVariableLayout.address c.1.1.arity ⟨.inl i,x⟩).val,
        NativeKSystemLayout.coefficientAddress_lt c.1.1.arity i x⟩ =
      c.2.val.getD (LocalAffineVariableLayout.address c.1.1.arity ⟨.inl i,x⟩).val
        NativeTargetPacking.defaultRoot := tupleData_target_getD c _

def test (d : RuntimeSupportTable.Data) (height : ℕ) (cs : List Root) : Bool :=
  if h : cs∈items (d,height) then
    (NativeKSystem.output (tupleData ⟨(d,height),⟨cs,h⟩⟩)).isSome
  else false

theorem test_of_mem (d : RuntimeSupportTable.Data) (height : ℕ) (cs : List Root)
    (h : cs∈items (d,height)) :
    test d height cs = (NativeKSystem.output (tupleData ⟨(d,height),⟨cs,h⟩⟩)).isSome :=
  dite_eq_left h

/-- A certified cell succeeds exactly when its literal target descriptors
represent every coefficient of the forward K transform. -/
theorem test_represents_iff (d : RuntimeSupportTable.Data) (height : ℕ) (cs : List Root)
    (h : cs∈items (d,height)) :
    test d height cs=true ↔
      ∀(i : Fin d.count) (x : Fin (d.arity i) → Bool),
        (cs.getD (LocalAffineVariableLayout.address d.arity ⟨.inl i,x⟩).val
          NativeTargetPacking.defaultRoot).Represents (sourceKBasis.action (d.G i) x : ℂ) := by
  rw [test_of_mem d height cs h]
  simpa only [tupleData_source,tupleData_target_getD] using
    NativeKSystem.output_represents_iff (tupleData ⟨(d,height),⟨cs,h⟩⟩)

def prepare (p : (Packed × ℕ) × List Root) : NativeKSystem.Input := (p.1.1,p.2)

/-- The runtime operation merely discards the height field and retains both
the complete source payload and the actual emitted candidate tuple. -/
def prepareComputes : Computes cellEncoding NativeKSystem.inputEncoding prepare :=
  pairComputes
    ((Wiring.firstComputes contextEncoding rootsEncoding).andThen
      (Wiring.firstComputes OriginalFamilyPackingMachine.encoding encodingNatBool))
    (Wiring.secondComputes contextEncoding rootsEncoding)

def witnessCellRuns : Runs NativeKSystem.inputEncoding WitnessOutput.resultEncoding
    (fun c : Cell => (RuntimeSupportTable.original c.1.1,c.2.val))
    (fun c => NativeKSystem.output (tupleData c)) where
  machine := NativeKSystem.witnessRuns.machine
  cost c := NativeKSystem.witnessRuns.cost (tupleData c)
  outputs c := by
    have h := NativeKSystem.witnessRuns.outputs (tupleData c)
    rw [tupleData_encode] at h
    exact h

/-- This uniform cell machine runs only on members of the certified runtime
catalogue. Neither an equation answer nor a malformed-root decision is input. -/
def cellsRuns : Runs cellEncoding encodingBoolBool
    (PromisedListMap.cellInput context items)
    (fun c : Cell => test c.1.1 c.1.2 c.2.val) :=
  (((Runs.ofComputes prepareComputes (PromisedListMap.cellInput context items)).comp
    witnessCellRuns).after (NativeCandidateSelection.presence WitnessOutput.outputEncoding)).congr
      (fun c => (test_of_mem c.1.1 c.1.2 c.2.val c.2.property).symm)

def coefficientCountRaw (p : Packed) : ℕ := (p.1.flatMap Prod.snd).length

theorem coefficientCountRaw_original (d : RuntimeSupportTable.Data) :
    coefficientCountRaw (RuntimeSupportTable.original d) = NativeKSystem.coefficientCount d := by
  exact NativeKSystemLayout.coefficientFlat_length d.arity d.input false

/-- Only stored vertex coefficients are counted. Native edge descriptors and
the fixed numerical constants do not enter the target tuple length. -/
def coefficientCountComputes : Computes OriginalFamilyPackingMachine.encoding encodingNatBool
    coefficientCountRaw := by
  let rows := OriginalFamilyPackingMachine.family.andThen
    (WireLists.mapComputes OriginalFamilyPackingMachine.vertexEncoding rootsEncoding Prod.snd
      (Wiring.secondComputes encodingNatBool rootsEncoding))
  let flat := rows.andThen (WireLists.flatten ComplexIsolation.CertificateMachine.rootEncoding)
  let length := flat.andThen
    (WireLists.lengthComputes ComplexIsolation.CertificateMachine.rootEncoding)
  exact congrComputes (length.andThen UnaryBinary.computes)
    (fun p => by simp only [Function.comp_apply]; rfl)

def itemsExecutes : Executes contextEncoding NativeCertifiedCatalogue.outputEncoding
    (fun p : Packed × ℕ => NativeCertifiedCatalogue.tuples (coefficientCountRaw p.1) p.2) :=
  (Executes.ofComputes (pairComputes
    ((Wiring.firstComputes OriginalFamilyPackingMachine.encoding encodingNatBool).andThen
      coefficientCountComputes)
    (Wiring.secondComputes OriginalFamilyPackingMachine.encoding encodingNatBool))).comp
      NativeCertifiedCatalogue.executes

/-- Both the varying coefficient count and the finite tuple list are produced
by physical programs from the source records and runtime search height. -/
def itemsRuns : Runs contextEncoding NativeCertifiedCatalogue.outputEncoding context items where
  machine := itemsExecutes.machine
  cost d := itemsExecutes.cost (context d)
  outputs d := by
    have h := itemsExecutes.outputs (context d)
    simpa only [context,coefficientCountRaw_original,items] using h

end
end Paper2.ExactInput.Recognition.NativeConverterCells

