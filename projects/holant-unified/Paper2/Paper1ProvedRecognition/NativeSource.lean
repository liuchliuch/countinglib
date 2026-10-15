import Paper2.Paper1ProvedRecognition.NativeKFamily
import Paper2.ExactInput.Recognition.NativeConverter
import Paper2.ExactInput.Recognition.NativeUniform

/-! One actual finite-control machine decides the native criterion directly
from every original valid literal table list. The runtime first certifies a
forward-K table, then executes the proved seven-way whole-family recognizer.
The transformed descriptors and stopping height are never caller inputs. -/
namespace Paper2.Paper1ProvedRecognition.NativeSource
open Computability Paper2.ExactInput
open Holant.Complexity Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1
open PhysicalFolds
open Paper2.ExactInput.Recognition
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The same original row layout with every desired table transformed by K. -/
def nativeData (L : Language) : RuntimeSupportTable.Data :=
  NativeTargetPacking.targetData (data L) (NativeKFamily.tables L)
    (NativeConverter.answer (data L)) (NativeConverter.answer_represents (data L))

def packed (L : Language) : OriginalFamilyPackingMachine.Input :=
  NativeConverter.packed (data L)

@[simp] theorem packed_exact (L : Language) :
    packed L=RuntimeSupportTable.original (nativeData L) :=
  NativeKFamily.target_packed L (NativeConverter.answer (data L))
    (NativeConverter.answer_represents (data L))

@[simp] theorem family_exact (L : Language) :
    RuntimeSevenDecision.family (nativeData L)=Paper2.kImage L :=
  NativeKFamily.target_family L (NativeConverter.answer (data L))
    (NativeConverter.answer_represents (data L))

def conversionRuns : Runs OriginalFamilyPackingMachine.encoding OriginalFamilyPackingMachine.encoding
    (fun L : Language => RuntimeSupportTable.original (data L)) packed :=
  RuntimeSupportTable.reindexRuns NativeConverter.runs data

def classificationRuns : Runs OriginalFamilyPackingMachine.encoding RuntimeSevenPrograms.outputEncoding
    packed (fun L => RuntimeSevenPrograms.output (nativeData L)) where
  machine := RuntimeSevenPrograms.executes.machine
  cost L := RuntimeSevenPrograms.executes.cost (nativeData L)
  outputs L := by simpa only [packed_exact] using RuntimeSevenPrograms.executes.outputs (nativeData L)

def decision (L : Language) : Bool := (RuntimeSevenPrograms.output (nativeData L)).1

def decisionRuns : Runs rawLanguageEncoding encodingBoolBool Subtype.val decision :=
  ((inputRuns.comp conversionRuns).comp classificationRuns).after
    (Wiring.firstComputes encodingBoolBool RuntimeSevenPrograms.detailsEncoding)

/-- One machine is chosen before all valid original native table inputs. Its
acceptance predicate is the exact whole-family criterion after forward K. -/
def recognizer : Paper2.Problem.NativeTractRecognizer where
  decision := decision
  machine := {
    tm := decisionRuns.machine.computer
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    outputsFun L := by
      simpa only [Equiv.refl,Language.bits,List.map_id] using (decisionRuns.outputs L).toTM2Outputs }
  finiteAlphabets _ := (inferInstance : Fintype Bool)
  correct L := by
    change (RuntimeSevenPrograms.output (nativeData L)).1=true ↔ _
    rw [RuntimeSevenDecision.output_correct,family_exact]
    exact (Paper2.Paper1Proved.tract_iff (Paper2.kImage L)).symm

/-- Source Theorem 9.2's native effectivity statement on the original bits. -/
theorem uniform_native_recognition :
    ∃ r : Paper2.Problem.NativeTractRecognizer,
      ∀ raw : RawLanguage, ∀ h : raw.Valid,
        ∃ b : Bool, ∃ steps : ℕ,
          (fun c : Option r.machine.tm.Cfg => c.bind r.machine.tm.step)^[steps]
            (some (r.initial raw))=some (r.final b) ∧
          r.machine.tm.step (r.final b)=none ∧
          (b=true ↔ Paper2.Tractable.Tract (Paper2.kImage (⟨raw,h⟩ : Language))) :=
  ⟨recognizer,recognizer.total_correct⟩

end
end Paper2.Paper1ProvedRecognition.NativeSource

