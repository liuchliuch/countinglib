import Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody.Bank
import Counting.Algorithm.KarpLubyRequest.Contract

/-! # Actual extraction and serialization of the three stored sample fields -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open FixedFieldMachines
open Counting.Algorithm.KarpLuby

set_option backward.isDefEq.respectTransparency false

theorem extract_field (i : Fin 3) (frame : Stack → List Bool) (field suffix : List Bool) :
    RunsExactly computer.step
      (config (.scan i) (tapes3 frame random (headerStack i) scratch (Encoding.frame field ++ suffix) [] []))
      (config (headerNext i) (tapes3 frame random (headerStack i) scratch suffix field []))
      (2 * (field.length + 1)) := by
  simpa only [← Contract.frame_eq, List.append_nil, config, cfg, Trial.initial] using
    Frame.extract_exact random (headerStack i) scratch
      (by fin_cases i <;> decide) (by decide) (by fin_cases i <;> decide)
      computer.step (.scan i) (.restore i) (headerNext i) .bad
      (by intro state tape; rfl) (by intro state tape; rfl)
      Trial.initial.2 frame field suffix []

private theorem rows_view (rows randomTape : List Bool) :
    tapes3 (ready [] [] [] [] []) random (headerStack 0) scratch randomTape rows [] =
      ready rows [] randomTape [] [] := by
  funext k
  cases k with
  | inl k => cases k <;> simp [tapes3, ready, tapes, random, headerStack, scratch, Trial.inputData, Trial.Data.tapes]
  | inr k => fin_cases k <;> simp [tapes3, ready, tapes, random, headerStack, scratch]

private theorem mass_view (rows mass randomTape : List Bool) :
    tapes3 (ready rows [] [] [] []) random (headerStack 1) scratch randomTape mass [] =
      ready rows mass randomTape [] [] := by
  funext k
  cases k with
  | inl k => cases k <;> simp [tapes3, ready, tapes, random, headerStack, scratch, Trial.inputData, Trial.Data.tapes]
  | inr k => fin_cases k <;> simp [tapes3, ready, tapes, random, headerStack, scratch]

private theorem acc_view (rows mass randomTape acc : List Bool) :
    tapes3 (ready rows mass [] [] []) random (headerStack 2) scratch randomTape acc [] =
      ready rows mass randomTape acc [] := by
  funext k
  cases k with
  | inl k => cases k <;> simp [tapes3, ready, tapes, random, headerStack, scratch, accumulator, Trial.inputData, Trial.Data.tapes]
  | inr k => fin_cases k <;> simp [tapes3, ready, tapes, random, headerStack, scratch, accumulator]

/-- The parser physically consumes exactly three frames and leaves every bit of
the random suffix on the trial input stack. -/
theorem prepare_exact (rows mass acc randomTape : List Bool) :
    RunsExactly computer.step
      (config (.scan 0) (ready [] [] (word rows mass acc randomTape) [] []))
      (config (.trial .clockMove) (ready rows mass randomTape acc []))
      (2 * (rows.length + mass.length + acc.length) + 6) := by
  have h0 := extract_field 0 (ready [] [] [] [] []) rows
    (Encoding.frame mass ++ Encoding.frame acc ++ randomTape)
  have h1 := extract_field 1 (ready rows [] [] [] []) mass
    (Encoding.frame acc ++ randomTape)
  have h2 := extract_field 2 (ready rows mass [] [] []) acc randomTape
  simp only [rows_view, headerNext, List.append_assoc] at h0
  simp only [mass_view, headerNext, List.append_assoc] at h1
  simp only [acc_view, headerNext, List.append_assoc] at h2
  convert (h0.trans h1).trans h2 using 1 <;> (try simp only [word, List.append_assoc]) <;> omega

theorem emit_field (i : Fin 3) (frame : Stack → List Bool) (field suffix : List Bool) :
    RunsExactly computer.step
      (config (.move i) (tapes3 frame (emitStack i) random scratch field suffix []))
      (config (emitNext i) (tapes3 frame (emitStack i) random scratch [] (Encoding.frame field ++ suffix) []))
      (2 * field.length + 3) := by
  simpa only [← Contract.frame_eq, config, cfg, Trial.initial] using
    FrameEmit.prepend_exact (emitStack i) random scratch
      (by fin_cases i <;> decide) (by fin_cases i <;> decide) (by decide)
      computer.step (.move i) (.delimiter i) (.emit i) (emitNext i)
      (by intro state tape; rfl) (by intro state tape; rfl) (by intro state tape; rfl)
      Trial.initial.2 frame field suffix

private theorem emit_acc_view (rows mass randomTape acc : List Bool) :
    tapes3 (ready rows mass [] [] []) (emitStack 0) random scratch acc randomTape [] =
      summed rows mass randomTape acc := by
  funext k
  cases k with
  | inl k => cases k <;> simp [tapes3, ready, summed, tapes, random, emitStack, scratch, addOutput, Trial.inputData, Trial.Data.tapes]
  | inr k => fin_cases k <;> simp [tapes3, ready, summed, tapes, random, emitStack, scratch, addOutput]

private theorem emit_mass_view (rows mass randomTape : List Bool) :
    tapes3 (ready rows [] [] [] []) (emitStack 1) random scratch mass randomTape [] =
      ready rows mass randomTape [] [] := by
  funext k
  cases k with
  | inl k => cases k <;> simp [tapes3, ready, tapes, random, emitStack, scratch, Trial.inputData, Trial.Data.tapes]
  | inr k => fin_cases k <;> simp [tapes3, ready, tapes, random, emitStack, scratch]

private theorem emit_rows_view (rows randomTape : List Bool) :
    tapes3 (ready [] [] [] [] []) (emitStack 2) random scratch rows randomTape [] =
      ready rows [] randomTape [] [] := by
  funext k
  cases k with
  | inl k => cases k <;> simp [tapes3, ready, tapes, random, emitStack, scratch, Trial.inputData, Trial.Data.tapes]
  | inr k => fin_cases k <;> simp [tapes3, ready, tapes, random, emitStack, scratch]

/-- Three real frame emitters consume their source fields, restore their order,
and halt with every stack except the shared input/output empty. -/
theorem serialize_exact (rows mass acc suffix : List Bool) :
    RunsExactly computer.step
      (config (.move 0) (summed rows mass suffix acc))
      (halted (word rows mass acc suffix))
      (2 * (rows.length + mass.length + acc.length) + 10) := by
  have h0 := emit_field 0 (ready rows mass [] [] []) acc suffix
  have h1 := emit_field 1 (ready rows [] [] [] []) mass (Encoding.frame acc ++ suffix)
  have h2 := emit_field 2 (ready [] [] [] [] []) rows
    (Encoding.frame mass ++ Encoding.frame acc ++ suffix)
  simp only [emit_acc_view, emitNext, List.append_assoc] at h0
  simp only [emit_mass_view, emitNext, List.append_assoc] at h1
  simp only [emit_rows_view, emitNext, List.append_assoc] at h2
  have h3 := runsExactly_one (finish_step (word rows mass acc suffix))
  simp only [word, List.append_assoc] at h3
  convert ((h0.trans h1).trans h2).trans h3 using 1 <;> (try simp only [word, List.append_assoc]) <;> omega

end Counting.Algorithm.KarpLubyRequest.Sampling.SampleBody
