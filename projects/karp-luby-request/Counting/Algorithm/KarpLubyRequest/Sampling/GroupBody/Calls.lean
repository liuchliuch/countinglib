import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Preparation

/-! # Full-bank calls to the real inner repetition and ordered append -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open FixedFieldMachines BinaryCompose
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

/-- This intermediate composition theorem uses only actual executions of the
supplied SampleBody machine at the visited states. The closed group endpoint
instantiates these premises with SampleBody.source_run and tape availability. -/
theorem loop_call {α : Type} (e : Computability.Encoding α Bool) (f : α → α) (time : α → ℕ)
    (n : ℕ) (x : α) (outer : Fin 6 → List Bool)
    (hr : ∀ i < n, Iteration.SourceRun SampleBody.machine (e.encode (f^[i] x))
      (e.encode (f (f^[i] x))) (time (f^[i] x))) :
    RunsExactly computer.step
      (config (.loop (Iteration.own SampleBody.machine 0)) (bank (encodeNat n) (e.encode x) outer))
      (config (.resultScan 0) (bank [] (e.encode (f^[n] x)) outer))
      (Iteration.ticks e f time n x) := by
  have ha : Embedded.Rel innerStacks Label.loop (.resultScan 0) (bank [] [] outer)
      (cfg (Iteration.own SampleBody.machine 0) SampleBody.machine.initial
        (Iteration.ready SampleBody.machine (encodeNat n) (e.encode x)))
      (config (.loop (Iteration.own SampleBody.machine 0)) (bank (encodeNat n) (e.encode x) outer)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro j hj
      cases j with
      | inl j => exact False.elim (hj j rfl)
      | inr j => rfl
  have hz : Embedded.Rel innerStacks Label.loop (.resultScan 0) (bank [] [] outer)
      (Iteration.finished SampleBody.machine (e.encode (f^[n] x)))
      (config (.resultScan 0) (bank [] (e.encode (f^[n] x)) outer)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; rfl
    · intro j hj
      cases j with
      | inl j => exact False.elim (hj j rfl)
      | inr j => rfl
  obtain ⟨ending, run, he⟩ := Embedded.run innerStacks Label.loop (.resultScan 0)
    (Iteration.program SampleBody.machine) program loop_code _ _ _ (bank [] [] outer) _ ha
    (Iteration.run_on SampleBody.machine e f time n x hr)
  rw [MachineCall.rel_unique innerStacks Label.loop (.resultScan 0) (bank [] [] outer)
    _ ending _ he hz] at run
  exact run

/-- Real frame removal separates the returned state into rows, mass, numerator
and literal random suffix. The saved sample count and history are untouched. -/
theorem extract_result (rowWord massWord sampleWord history result randomWord : List Bool) :
    RunsExactly computer.step (config (.resultScan 0)
      (bank [] (SampleBody.word rowWord massWord result randomWord)
        (fields [] [] sampleWord history [] [])))
      (config (.append .append) (bank [] randomWord
        (fields rowWord massWord sampleWord history result [])))
      (2 * (rowWord.length + massWord.length + result.length) + 6) := by
  have h0 := extract_field (.resultScan 0) (.resultRestore 0) (.resultScan 1) 0 (by decide)
    (by intro state tape; rfl) (by intro state tape; rfl) [] rowWord
    (Encoding.frame massWord ++ Encoding.frame result ++ randomWord)
    (fields [] [] sampleWord history [] []) rfl rfl
  have h1 := extract_field (.resultScan 1) (.resultRestore 1) (.resultScan 2) 1 (by decide)
    (by intro state tape; rfl) (by intro state tape; rfl) [] massWord
    (Encoding.frame result ++ randomWord) (fields rowWord [] sampleWord history [] []) rfl rfl
  have h2 := extract_field (.resultScan 2) (.resultRestore 2) (.append .append) 4 (by decide)
    (by intro state tape; rfl) (by intro state tape; rfl) [] result randomWord
    (fields rowWord massWord sampleWord history [] []) rfl rfl
  simp only [fields_update] at h0 h1 h2
  norm_num [Fin.ext_iff] at h0 h1 h2
  dsimp only [fields] at h0 h1 h2
  norm_num at h0 h1 h2
  convert (h0.trans h1).trans h2 using 1 <;>
    first | rfl | (simp only [SampleBody.word, fields, List.append_assoc] <;> omega) | omega

/-- Appending runs the canonical physical program on the materialized
numerator. Arbitrary raw history is retained as the suffix of its new frame. -/
theorem append_result (rowWord massWord sampleWord history result randomWord : List Bool) :
    RunsExactly computer.step (config (.append .append)
      (bank [] randomWord (fields rowWord massWord sampleWord history result [])))
      (config (.outerMove 0) (ready rowWord massWord sampleWord
        ((Encoding.frame result).reverse ++ history) randomWord)) (result.length + 1) := by
  let before := bank [] randomWord (fields rowWord massWord sampleWord history result [])
  let after := ready rowWord massWord sampleWord ((Encoding.frame result).reverse ++ history) randomWord
  have ha : Embedded.Rel appendStacks Label.append (.outerMove 0) before
      (StateAdapter.cfg (MachineCall.unitState Memory) SampleBody.machine.initial
        (cfg GroupOutput.Label.append () (GroupOutput.bank result history [] sampleWord)))
      (config (.append .append) before) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro j hj; rfl
  have hz : Embedded.Rel appendStacks Label.append (.outerMove 0) before
      (StateAdapter.cfg (MachineCall.unitState Memory) SampleBody.machine.initial
        (⟨none, (none, ()), GroupOutput.bank [] ((Encoding.frame result).reverse ++ history) [] sampleWord⟩ :
          GroupOutput.computer.Cfg))
      (config (.outerMove 0) after) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro k; fin_cases k <;> rfl
    · intro j hj
      cases j with
      | inl j => rfl
      | inr j =>
        fin_cases j
        · rfl
        · rfl
        · exact False.elim (hj 3 rfl)
        · exact False.elim (hj 1 rfl)
        · exact False.elim (hj 0 rfl)
        · exact False.elim (hj 2 rfl)
  exact MachineCall.run appendStacks Label.append (.outerMove 0) (MachineCall.unitState Memory)
    GroupOutput.program program append_code SampleBody.machine.initial before _ _ _ _ _ ha hz
    (GroupOutput.append_word result history sampleWord)

end Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
