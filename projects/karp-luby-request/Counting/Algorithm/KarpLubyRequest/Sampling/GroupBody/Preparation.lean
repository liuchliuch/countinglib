import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Frames

/-! # Physical preparation and serialization around the inner sample loop -/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open FixedFieldMachines BinaryCompose
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

theorem fields_update (a b c d e w value : List Bool) (i : Fin 6) :
    Function.update (fields a b c d e w) i value =
      fields (if i = 0 then value else a) (if i = 1 then value else b)
        (if i = 2 then value else c) (if i = 3 then value else d)
        (if i = 4 then value else e) (if i = 5 then value else w) := by
  funext j
  fin_cases i <;> fin_cases j <;> rfl

private theorem empty_frame : Encoding.frame [] = [false] := rfl

theorem fields_empty : emptyFields = fields [] [] [] [] [] [] := by
  funext j; fin_cases j <;> rfl

/-- All four words are removed by the actual returning frame scanner. -/
theorem parse (rowWord massWord sampleWord history randomWord : List Bool) :
    RunsExactly computer.step
      (config (.scan 0) (bank [] (word rowWord massWord sampleWord history randomWord) emptyFields))
      (config .countMove (ready rowWord massWord sampleWord history randomWord))
      (2 * (rowWord.length + massWord.length + sampleWord.length + history.length) + 8) := by
  have h0 := header_extract 0 [] rowWord
    (Encoding.frame massWord ++ Encoding.frame sampleWord ++ Encoding.frame history ++ randomWord)
    (fields [] [] [] [] [] []) rfl rfl
  have h1 := header_extract 1 [] massWord
    (Encoding.frame sampleWord ++ Encoding.frame history ++ randomWord)
    (fields rowWord [] [] [] [] []) rfl rfl
  have h2 := header_extract 2 [] sampleWord (Encoding.frame history ++ randomWord)
    (fields rowWord massWord [] [] [] []) rfl rfl
  have h3 := header_extract 3 [] history randomWord
    (fields rowWord massWord sampleWord [] [] []) rfl rfl
  simp only [fields_update] at h0 h1 h2 h3
  norm_num [Fin.ext_iff] at h0 h1 h2 h3
  dsimp only [fields, headerNext] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  convert ((h0.trans h1).trans h2).trans h3 using 1 <;>
    first | rfl | (simp only [word, fields_empty, fields, List.append_assoc] <;> omega) | omega

/-- The original canonical samples word is retained while its actual copy is
placed on the inner repeat compiler's countdown stack. -/
theorem copy_samples (randomWord : List Bool) (f : Fin 6 → List Bool) (hwork : f 5 = []) :
    RunsExactly computer.step (config .countMove (bank [] randomWord f))
      (config .innerZero (bank (f 2) randomWord f)) (2 * ((f 2).length + 1)) := by
  have h := copy_exact samples counter scratch (by intro h; cases h)
    (fun h => (show (2 : Fin 6) ≠ 5 by decide) (Sum.inr.inj h)) (by intro h; cases h)
    computer.step .countMove .countRestore .innerZero
    (by intro state tape; rfl) (by intro state tape; rfl)
    SampleBody.machine.initial (bank [] randomWord f) hwork
  simp only [samples, bank_field, bank_counter, List.append_nil, update_counter] at h
  exact h

theorem zero_step (count randomWord : List Bool) (f : Fin 6 → List Bool) :
    computer.step (config .innerZero (bank count randomWord f)) =
      some (config (.innerMove 0) (bank count (false :: randomWord) f)) := by
  change some (⟨some (.innerMove 0), initial,
    Function.update (bank count randomWord f) random (false :: bank count randomWord f random)⟩ : computer.Cfg) = _
  rw [bank_random, update_random]
  rfl

/-- The zero accumulator and both retained physical fields are emitted into
the exact SampleBody input codec. This also covers a zero sample countdown. -/
theorem prepare_inner (rowWord massWord sampleWord history randomWord : List Bool) :
    RunsExactly computer.step (config .innerZero
      (bank sampleWord randomWord (fields rowWord massWord sampleWord history [] [])))
      (config (.loop (Iteration.own SampleBody.machine 0))
        (bank sampleWord (SampleBody.word rowWord massWord [] randomWord)
          (fields [] [] sampleWord history [] [])))
      (2 * (rowWord.length + massWord.length) + 7) := by
  have h0 := runsExactly_one (zero_step sampleWord randomWord
    (fields rowWord massWord sampleWord history [] []))
  have h1 := inner_emit 0 sampleWord (false :: randomWord)
    (fields rowWord massWord sampleWord history [] []) rfl
  have h2 := inner_emit 1 sampleWord (Encoding.frame massWord ++ false :: randomWord)
    (fields rowWord [] sampleWord history [] []) rfl
  simp only [fields_update] at h1 h2
  norm_num [Fin.ext_iff] at h1 h2
  dsimp only [fields, innerNext] at h1 h2
  norm_num at h1 h2
  convert (h0.trans h1).trans h2 using 1 <;>
    first | rfl | (simp only [SampleBody.word, empty_frame, List.singleton_append, List.append_assoc, fields] <;> omega) | omega

/-- Four ordinary frame emissions reconstruct the group state and clear all
six outer work stacks, followed by the actual final halt. -/
theorem serialize (rowWord massWord sampleWord history randomWord : List Bool) :
    RunsExactly computer.step (config (.outerMove 0)
      (ready rowWord massWord sampleWord history randomWord))
      (halted (word rowWord massWord sampleWord history randomWord))
      (2 * (rowWord.length + massWord.length + sampleWord.length + history.length) + 13) := by
  have h0 := outer_emit 0 [] randomWord (fields rowWord massWord sampleWord history [] []) rfl
  have h1 := outer_emit 1 [] (Encoding.frame history ++ randomWord)
    (fields rowWord massWord sampleWord [] [] []) rfl
  have h2 := outer_emit 2 [] (Encoding.frame sampleWord ++ Encoding.frame history ++ randomWord)
    (fields rowWord massWord [] [] [] []) rfl
  have h3 := outer_emit 3 []
    (Encoding.frame massWord ++ Encoding.frame sampleWord ++ Encoding.frame history ++ randomWord)
    (fields rowWord [] [] [] [] []) rfl
  simp only [fields_update] at h0 h1 h2 h3
  norm_num [Fin.ext_iff] at h0 h1 h2 h3
  dsimp only [fields, outerNext] at h0 h1 h2 h3
  norm_num at h0 h1 h2 h3
  have last := runsExactly_one (finish_step (word rowWord massWord sampleWord history randomWord))
  rw [fields_empty] at last
  simp only [word, fields, List.append_assoc] at last
  convert (((h0.trans h1).trans h2).trans h3).trans last using 1 <;>
    first | rfl | (simp only [word, ready, fields, List.append_assoc] <;> omega) | omega

end Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody
