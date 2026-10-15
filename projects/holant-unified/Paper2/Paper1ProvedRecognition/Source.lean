import Paper2.Paper1ProvedRecognition.Codec
import Paper2.Paper1ProvedCriteria
import Holant.Proofs.Recognition.RuntimeSevenDecision
import Paper2.ExactInput.Recognition.Uniform

/-! One actual finite-alphabet machine for every valid literal Paper 2 table
list. Its input controller regroups the rectangle codec and permutes each dense
table by an explicit binary index, then executes the proved Paper 1 varying
layout recognizer and projects its Boolean output. Semantic validity supplies
the correctness proof, with no runtime certificate or chosen classification. -/
namespace Paper2.Paper1ProvedRecognition
open Computability Paper2.ExactInput
open Holant.Complexity Holant.Complexity.BinaryCompose Holant.Complexity.FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1
open PhysicalFolds
noncomputable section

theorem vertex_exact (c : SignatureCode) (h : c.Valid) :
    vertex c = (c.arity,(SparseTransform.allWords c.arity).map (fun x => root (c.entry h x))) := by
  unfold vertex
  rw [RationalTableMachine.words_eq,List.map_map]
  congr 1
  apply List.map_congr_left
  intro x hx
  simp only [Function.comp_apply]
  rw [wordValue_ofFn]
  have hi : (wordIndex c.arity x).val < c.entries.length := by
    rw [h.1]
    exact (wordIndex c.arity x).isLt
  simp only [base,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some,
    SignatureCode.entry,List.get_eq_getElem,Fin.val_cast]

def data (L : Language) : RuntimeSupportTable.Data where
  count := L.count
  arity i := (L.code i).arity
  G i := (L.code i).denote (L.code_valid i)
  input i x := root ((L.code i).entry (L.code_valid i) x)
  represented i x := (represents _ _).mpr ((L.code i).denote_spec (L.code_valid i) _).1

theorem packed_exact (L : Language) : packed L.val = RuntimeSupportTable.original (data L) := by
  unfold packed RuntimeSupportTable.original OriginalFamilyPackingSource.fromSource
  congr 1
  rw [← List.ofFn_get L.val, List.map_ofFn]
  change List.ofFn (fun i : Fin L.count => vertex (L.code i)) = _
  rw [← List.ofFn_id,List.map_ofFn]
  apply congrArg List.ofFn
  funext i
  rw [vertex_exact _ (L.code_valid i)]
  rfl

private theorem signature_cast {n m : ℕ} (h : n = m)
    (f : Paper2.Signature Paper2.Tractable.AlgebraicComplex m) :
    (⟨n,fun x => f (fun j => x (Fin.cast h.symm j))⟩ :
      Paper2.AnySignature Paper2.Tractable.AlgebraicComplex) = ⟨m,f⟩ := by
  cases h
  rfl

@[simp] theorem data_family (L : Language) : RuntimeSevenDecision.family (data L) = L.family := by
  apply congrArg Set.range
  funext i
  exact (signature_cast (L.arity_index i) ((L.code i).denote (L.code_valid i))).symm

def decision (L : Language) : Bool := (RuntimeSevenPrograms.output (data L)).1

def inputRuns : Runs rawLanguageEncoding OriginalFamilyPackingMachine.encoding
    Subtype.val (fun L : Language => RuntimeSupportTable.original (data L)) where
  machine := packedExecutes.machine
  cost L := packedExecutes.cost L.val
  outputs L := by simpa only [packed_exact] using packedExecutes.outputs L.val

def classificationRuns : Runs OriginalFamilyPackingMachine.encoding RuntimeSevenPrograms.outputEncoding
    (fun L : Language => RuntimeSupportTable.original (data L))
    (fun L => RuntimeSevenPrograms.output (data L)) :=
  RuntimeSupportTable.reindexRuns RuntimeSevenPrograms.executes data

def decisionRuns : Runs rawLanguageEncoding encodingBoolBool Subtype.val decision :=
  (inputRuns.comp classificationRuns).after
    (Wiring.firstComputes encodingBoolBool RuntimeSevenPrograms.detailsEncoding)

def recognizer : Paper2.Problem.TractRecognizer where
  decision := decision
  machine := {
    tm := decisionRuns.machine.computer
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    outputsFun L := by
      simpa only [Equiv.refl,Language.bits,List.map_id] using (decisionRuns.outputs L).toTM2Outputs }
  finiteAlphabets _ := (inferInstance : Fintype Bool)
  correct L := by
    change (RuntimeSevenPrograms.output (data L)).1 = true ↔ _
    rw [RuntimeSevenDecision.output_correct,data_family]
    exact (Paper2.Paper1Proved.tract_iff L.family).symm

/-- Unconditional uniform recognition; all Paper 1 record fields are discharged
by the actual finite machine above. -/
theorem uniform_recognition :
    ∃ r : Paper2.Problem.TractRecognizer,
      ∀ raw : RawLanguage, ∀ h : raw.Valid,
        ∃ b : Bool, ∃ steps : ℕ,
          (fun c : Option r.machine.tm.Cfg => c.bind r.machine.tm.step)^[steps]
            (some (r.initial raw)) = some (r.final b) ∧
          r.machine.tm.step (r.final b) = none ∧
          (b = true ↔ Paper2.Tractable.Tract (Language.family ⟨raw,h⟩)) :=
  ⟨recognizer,recognizer.total_correct⟩

end
end Paper2.Paper1ProvedRecognition
