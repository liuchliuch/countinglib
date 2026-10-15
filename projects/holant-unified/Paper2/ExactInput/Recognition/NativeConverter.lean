import Paper2.ExactInput.Recognition.NativeConverterCells
import Paper2.ExactInput.Recognition.NativeExpectedTable
import Paper2.ExactInput.Recognition.NativeSearchStage
import Paper2.ExactInput.Recognition.NativeSearchController
import Paper2.ExactInput.Recognition.NativeKSystemOrdinal

/-! A single physical converter from every valid original family to a certified
forward-K family table. All descriptors are emitted by a total finite checker
before any root-system search; completeness proves termination. -/
namespace Paper2.ExactInput.Recognition.NativeConverter
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open PhysicalFolds
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Root := NativeCertifiedCatalogue.Root
abbrev packedEncoding := OriginalFamilyPackingMachine.encoding
abbrev rootsEncoding := NativeCertifiedCatalogue.rootsEncoding

def tests (d : NativeConverterCells.Datum) : List Root → Bool :=
  NativeConverterCells.test d.1 d.2

def stage (d : NativeConverterCells.Datum) : Option (List Root) :=
  NativeSearchStage.stage NativeConverterCells.items tests d

def stagesRuns : Runs NativeConverterCells.contextEncoding
    (Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding rootsEncoding)
    NativeConverterCells.context stage :=
  NativeSearchStage.runs NativeConverterCells.contextEncoding rootsEncoding
    NativeConverterCells.context NativeConverterCells.items tests
    NativeConverterCells.itemsRuns NativeConverterCells.cellsRuns

theorem termination (d : RuntimeSupportTable.Data) :
    ∃ height, (stage (d,height)).isSome=true := by
  obtain ⟨cs,H,hH,hrep⟩ := NativeExpectedTable.exists_tuple d
  have hc : cs ∈ NativeConverterCells.items (d,H) := hH H le_rfl
  refine ⟨H,(NativeSearchStage.isSome_iff NativeConverterCells.items tests (d,H)).mpr ?_⟩
  refine ⟨cs,hc,?_⟩
  exact (NativeConverterCells.test_represents_iff d H cs hc).mpr hrep

def answer (d : RuntimeSupportTable.Data) : List Root :=
  (NativeSearchController.result stage termination d).getD []

private theorem selected_eq (d : RuntimeSupportTable.Data) :
    NativeSearchController.result stage termination d=some (answer d) := by
  have hh := NativeSearchController.result_some stage termination d
  cases h : NativeSearchController.result stage termination d with
  | none => simp [h] at hh
  | some cs => simp [answer,h]

theorem answer_mem (d : RuntimeSupportTable.Data) :
    answer d ∈ NativeConverterCells.items (d,NativeSearchController.height stage termination d) :=
  (NativeSearchStage.some_mem NativeConverterCells.items tests (selected_eq d)).1

theorem answer_test (d : RuntimeSupportTable.Data) :
    NativeConverterCells.test d (NativeSearchController.height stage termination d) (answer d)=true :=
  (NativeSearchStage.some_mem NativeConverterCells.items tests (selected_eq d)).2

theorem answer_length (d : RuntimeSupportTable.Data) :
    (answer d).length=NativeKSystem.coefficientCount d :=
  NativeCertifiedCatalogue.tuple_length (answer_mem d)

/-- Every returned coefficient is the exact forward-K coefficient, including
zeros and nullary rows. A successful equation check is proved, not assumed. -/
theorem answer_represents (d : RuntimeSupportTable.Data) :
    ∀(i : Fin d.count) (x : Fin (d.arity i) → Bool),
      ((answer d).getD (NativeTargetPacking.targetOrdinal d i x)
        NativeTargetPacking.defaultRoot).Represents (sourceKBasis.action (d.G i) x : ℂ) := by
  intro i x
  rw [NativeKSystemLayout.targetOrdinal_address]
  exact ((NativeConverterCells.test_represents_iff d _ (answer d) (answer_mem d)).mp
    (answer_test d)) i x

def answerRuns : Runs packedEncoding rootsEncoding RuntimeSupportTable.original answer :=
  (NativeSearchController.runs packedEncoding rootsEncoding RuntimeSupportTable.original
    stage stagesRuns termination).after (NativeCandidateSelection.getDComputes rootsEncoding [])

def packed (d : RuntimeSupportTable.Data) : OriginalFamilyPackingMachine.Input :=
  NativeTargetPacking.reshape (RuntimeSupportTable.original d,answer d)

def reshapeRuns : Runs NativeTargetPacking.inputEncoding packedEncoding
    (fun d => (RuntimeSupportTable.original d,answer d)) packed where
  machine := NativeTargetPacking.executes.machine
  cost d := NativeTargetPacking.executes.cost (RuntimeSupportTable.original d,answer d)
  outputs d := NativeTargetPacking.executes.outputs (RuntimeSupportTable.original d,answer d)

/-- No transformed table, common field, certificate, stopping height, or
success bit is encoded in the original varying-family input. -/
def runs : Runs packedEncoding packedEncoding RuntimeSupportTable.original packed :=
  ((Runs.ofComputes (identityComputes packedEncoding) RuntimeSupportTable.original).pair answerRuns).comp reshapeRuns

end
end Paper2.ExactInput.Recognition.NativeConverter

