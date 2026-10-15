import Counting.Algorithm.KarpLubyRequest.Evaluation.Front

/-! Parse the actual outer-loop state into the median caller's physical bank. -/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

def returnIndex (i : Fin 4) : Fin 6 :=
  match i.val with | 0 => 0 | 1 => 1 | 2 => 2 | _ => 4

theorem returnedField_eq (i : Fin 4) : returnedField i = extra (returnIndex i) := by
  fin_cases i <;> rfl

theorem extract_returned (i : Fin 4) (word suffix : List Bool) (fields : Fin 6 → List Bool)
    (hd : fields (returnIndex i) = []) (ht : fields 5 = []) :
    RunsExactly computer.step
      (configuration (.resultScan i) initial (frontData [] (Encoding.frame word ++ suffix) fields))
      (configuration (returnedNext i) initial
        (frontData [] suffix (Function.update fields (returnIndex i) word)))
      (2 * (word.length+1)) := by
  have he : (frontData [] (Encoding.frame word ++ suffix) fields).tapes (returnedField i) = [] := by
    rw [returnedField_eq, front_field]
    exact hd
  have h := returned_extract i initial.2 (frontData [] (Encoding.frame word ++ suffix) fields).tapes
    word suffix (front_random _ _ _) he ht
  rw [returnedField_eq, front_update_random, front_update_field] at h
  exact h

theorem parse_results (r m s g history tape : List Bool) :
    RunsExactly computer.step
      (configuration (.resultScan 0) initial
        (frontData [] (Sampling.GroupBody.word r m s history tape) (fieldWords [] [] [] g [] [])))
      (configuration (.groupFinish .reverse) initial
        (frontData [] tape (fieldWords r m s g history [])))
      (2*(r.length+m.length+s.length+history.length)+8) := by
  have h0 := extract_returned 0 r (Encoding.frame m ++ Encoding.frame s ++ Encoding.frame history ++ tape)
    (fieldWords [] [] [] g [] []) rfl rfl
  have h1 := extract_returned 1 m (Encoding.frame s ++ Encoding.frame history ++ tape)
    (fieldWords r [] [] g [] []) rfl rfl
  have h2 := extract_returned 2 s (Encoding.frame history ++ tape) (fieldWords r m [] g [] []) rfl rfl
  have h3 := extract_returned 3 history tape (fieldWords r m s g [] []) rfl rfl
  dsimp only [returnIndex] at h0 h1 h2 h3
  simp only [fieldWords_update] at h0 h1 h2 h3
  norm_num [Fin.ext_iff] at h0 h1 h2 h3
  dsimp only [returnedNext] at h0 h1 h2 h3
  have h := ((h0.trans h1).trans h2).trans h3
  have ht : 2*(history.length+1)+(2*(s.length+1)+(2*(m.length+1)+2*(r.length+1))) =
      2*(r.length+m.length+s.length+history.length)+8 := by omega
  rw [ht] at h
  dsimp only [FinTM2.step] at h ⊢
  simpa only [Sampling.GroupBody.word, List.append_assoc] using h

end Counting.Algorithm.KarpLubyRequest.Evaluation
