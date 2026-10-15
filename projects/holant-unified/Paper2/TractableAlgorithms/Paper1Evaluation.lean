import Paper2.TractableAlgorithms.Paper1Machine
import Paper2.Paper1ProvedGraph
import Paper2.Paper1ProvedCriteria
import Holant.Proofs.Algorithms.ReturnedLPTractSourceV2
import Paper2.FixedFieldOutput.Holography

/-! Unconditional seven-clause evaluation by the already proved Paper 1 finite
programs. All input labels, ordered incidences, zero and nullary vertices are
retained. The program needs no accepted-result record. A fixed rational matrix
converts the proved evaluator's chosen field basis to the basis of the original
literal Paper 2 family. -/
namespace Paper2.TractableAlgorithms
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.Complexity.BinaryCompose Paper2.FixedFieldOutput
noncomputable section

/-- The original-family machine handles all seven clauses, with all family-wide
sign, basis and EO witnesses transported before the graph input is supplied. -/
def ordinaryComputes (L : Language) (h : Tract L.family) :
    Computes (inputEncoding L) (answerEncoding L) (answer .ordinary L) := by
  let G := Paper1Proved.signatures L
  let E := Holant.LocalDrafts.MainChain.KSourceTransport.equalityEdges
  let F := Holant.LocalDrafts.MainChain.OriginalFamily.presentation G E
  let f := Holant.LocalDrafts.MainChain.OriginalFamily.value G E
  let m := Holant.LocalDrafts.MainChain.ReturnedLPTractSourceV2.computes G
    ((Paper1Proved.tract_iff L.family).mp h)
  apply Paper1Machine.fieldEvaluation L .ordinary
    (Holant.Complexity.RawClosedNetwork.validatedEncoding L.count 1 L.arity)
    F f
    (Holant.Algebraic.familyField
      (Holant.LocalDrafts.MainChain.OriginalFamily.coefficient G E)).val.toLinearMap
    m (Paper1Proved.input L) (Paper1Proved.input_bytes L)
  intro input
  exact Paper1Proved.value .ordinary L input

theorem ordinary_booleanFP_of_tract (L : Language) (h : Tract L.family) :
    BooleanFP .ordinary L := ⟨ordinaryComputes L h⟩

theorem ordinary_inFP_of_tract (L : Language) (h : Tract L.family) :
    FixedFieldOutput.InFP .ordinary L := (ordinary_booleanFP_of_tract L h).inFP

/-- Classification preprocessing changes only the structural criterion. The
machine still receives every original label, including zero and nullary labels. -/
theorem ordinary_booleanFP_of_seven_alternatives (L : Language)
    (h : TractCore (preprocess L.family)) : BooleanFP .ordinary L := by
  apply ordinary_booleanFP_of_tract L
  exact ⟨L.family_finite.subset (fun _ hf => hf.1), h⟩

/-- The normalized holographic identity is exact on the original graph bytes.
Both fixed-field coordinate conversions execute proved rational programs. -/
theorem native_booleanFP_of_tract (L : Language) (h : Tract (kImage L)) :
    BooleanFP .nativeX L :=
  (FixedFieldOutput.native_booleanFP_iff L).mpr
    (ordinary_booleanFP_of_tract (ExactInput.Computation.kLanguage L) (by simpa using h))

theorem native_inFP_of_tract (L : Language) (h : Tract (kImage L)) :
    FixedFieldOutput.InFP .nativeX L := (native_booleanFP_of_tract L h).inFP

theorem native_booleanFP_of_tractX (L : Language) (h : TractX (kImage L)) :
    BooleanFP .nativeX L := native_booleanFP_of_tract L h.tract

theorem native_booleanFP_of_seven_alternatives (L : Language)
    (h : TractCore (preprocess (kImage L))) : BooleanFP .nativeX L := by
  apply native_booleanFP_of_tract L
  exact ⟨(L.family_finite.image _).subset (fun _ hf => hf.1), h⟩

/-- Expose the actual finite transition bound in the literal edge-assignment
semantics. This is the same constructed evaluator as `ordinaryComputes`. -/
theorem ordinary_machine_on_literal_graphs (L : Language) (h : Tract L.family) :
    ∃ m : Computes (inputEncoding L) (answerEncoding L) (answer .ordinary L),
      ∀ G : Instance L,
        (L.fieldPresentation.decode (answer .ordinary L G) : AlgebraicComplex) =
          value .ordinary L G ∧
        ∃ steps : ℕ,
          steps ≤ m.time.eval ((inputEncoding L).encode G).length ∧
          (fun c : Option m.machine.computer.Cfg => c.bind m.machine.computer.step)^[steps]
            (some (Turing.initList m.machine.computer ((inputEncoding L).encode G))) =
              some (Turing.haltList m.machine.computer ((answerEncoding L).encode
                (answer .ordinary L G))) := by
  let m := ordinaryComputes L h
  exact ⟨m, fun G => ⟨answer_correct .ordinary L G,
    (m.outputs G).steps, (m.outputs G).steps_le_m, (m.outputs G).evals_in_steps⟩⟩

end
end Paper2.TractableAlgorithms
