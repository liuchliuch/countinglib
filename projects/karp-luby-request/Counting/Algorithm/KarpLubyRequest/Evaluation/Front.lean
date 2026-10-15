import Counting.Algorithm.KarpLubyRequest.Evaluation.Frames
import Counting.Algorithm.KarpLubyRequest.Sampling.GroupBody.Bank

/-! Physical input preparation for the outer group countdown. -/
namespace Counting.Algorithm.KarpLubyRequest.Evaluation
open Turing Computability Holant.Complexity StackProtocol BinaryCompose
open Counting.Algorithm.KarpLuby
set_option backward.isDefEq.respectTransparency false

def frontData (count tape : List Bool) (fields : Fin 6 → List Bool) : Data :=
  { outer := Iteration.ready Sampling.GroupBody.machine count tape, fields := fields }

theorem front_random (count tape : List Bool) (fields : Fin 6 → List Bool) :
    (frontData count tape fields).tapes random = tape :=
  wordTape_at Sampling.GroupBody.random tape

theorem front_counter (count tape : List Bool) (fields : Fin 6 → List Bool) :
    (frontData count tape fields).tapes counter = count := rfl

theorem front_field (count tape : List Bool) (fields : Fin 6 → List Bool) (i : Fin 6) :
    (frontData count tape fields).tapes (extra i) = fields i := rfl

theorem front_update_random (count tape replacement : List Bool) (fields : Fin 6 → List Bool) :
    Function.update (frontData count tape fields).tapes random replacement =
      (frontData count replacement fields).tapes := by
  funext j
  rcases j with (j | j) | (j | (j | j))
  · fin_cases j <;> rfl
  · by_cases hj : j = Sampling.GroupBody.random
    · subst j; rfl
    · have ho : (Sum.inl (Sum.inr j) : Stack) ≠ random := by
        intro h; exact hj (Sum.inr.inj (Sum.inl.inj h))
      rw [Function.update_of_ne ho]
      exact (wordTape_other Sampling.GroupBody.random j tape hj).trans
        (wordTape_other Sampling.GroupBody.random j replacement hj).symm
  all_goals rfl

theorem front_update_counter (count tape replacement : List Bool) (fields : Fin 6 → List Bool) :
    Function.update (frontData count tape fields).tapes counter replacement =
      (frontData replacement tape fields).tapes := by
  funext j
  rcases j with (j | j) | (j | (j | j))
  · fin_cases j <;> rfl
  all_goals rfl

theorem front_update_field (count tape : List Bool) (fields : Fin 6 → List Bool)
    (i : Fin 6) (word : List Bool) :
    Function.update (frontData count tape fields).tapes (extra i) word =
      (frontData count tape (Function.update fields i word)).tapes :=
  update_field (frontData count tape fields) i word

theorem fieldWords_update (r m s g a work value : List Bool) (i : Fin 6) :
    Function.update (fieldWords r m s g a work) i value =
      fieldWords (if i=0 then value else r) (if i=1 then value else m)
        (if i=2 then value else s) (if i=3 then value else g)
        (if i=4 then value else a) (if i=5 then value else work) := by
  funext j
  fin_cases i <;> fin_cases j <;> rfl

theorem extract_front (i : Fin 4) (count word suffix : List Bool) (fields : Fin 6 → List Bool)
    (hd : fields ⟨i.val, by omega⟩ = []) (ht : fields 5 = []) :
    RunsExactly computer.step
      (configuration (.scan i) initial (frontData count (Encoding.frame word ++ suffix) fields))
      (configuration (headerNext i) initial
        (frontData count suffix (Function.update fields ⟨i.val, by omega⟩ word)))
      (2 * (word.length + 1)) := by
  have h := header_extract i initial.2 (frontData count (Encoding.frame word ++ suffix) fields).tapes
    word suffix (front_random _ _ _) hd ht
  dsimp only [headerField] at h
  rw [front_update_random, front_update_field] at h
  exact h

theorem parse_headers (r m s g tape : List Bool) :
    RunsExactly computer.step
      (configuration (.scan 0) initial (frontData []
        (Encoding.frame r ++ Encoding.frame m ++ Encoding.frame s ++ Encoding.frame g ++ tape)
        (fieldWords [] [] [] [] [] [])))
      (configuration .countMove initial (frontData [] tape (fieldWords r m s g [] [])))
      (2*(r.length+m.length+s.length+g.length)+8) := by
  have h0 := extract_front 0 [] r (Encoding.frame m ++ Encoding.frame s ++ Encoding.frame g ++ tape)
    (fieldWords [] [] [] [] [] []) rfl rfl
  have h1 := extract_front 1 [] m (Encoding.frame s ++ Encoding.frame g ++ tape)
    (fieldWords r [] [] [] [] []) rfl rfl
  have h2 := extract_front 2 [] s (Encoding.frame g ++ tape) (fieldWords r m [] [] [] []) rfl rfl
  have h3 := extract_front 3 [] g tape (fieldWords r m s [] [] []) rfl rfl
  simp only [fieldWords_update] at h0 h1 h2 h3
  norm_num [Fin.ext_iff] at h0 h1 h2 h3
  dsimp only [headerNext] at h0 h1 h2 h3
  have h := ((h0.trans h1).trans h2).trans h3
  have ht : 2*(g.length+1)+(2*(s.length+1)+(2*(m.length+1)+2*(r.length+1))) =
      2*(r.length+m.length+s.length+g.length)+8 := by omega
  rw [ht] at h
  dsimp only [FinTM2.step] at h ⊢
  simpa only [List.append_assoc] using h

theorem emit_front (i : Fin 3) (count tape : List Bool) (fields : Fin 6 → List Bool)
    (ht : fields 5 = []) :
    RunsExactly computer.step (configuration (.emitMove i) initial (frontData count tape fields))
      (configuration (emitNext i) initial
        (frontData count (Encoding.frame (fields ⟨2-i.val, by omega⟩) ++ tape)
          (Function.update fields ⟨2-i.val, by omega⟩ [])))
      (2*(fields ⟨2-i.val, by omega⟩).length+3) := by
  have h := header_emit i initial.2 (frontData count tape fields).tapes ht
  dsimp only [emitField] at h
  rw [front_field, front_random, front_update_field, front_update_random] at h
  exact h

theorem copy_front (tape : List Bool) (fields : Fin 6 → List Bool) (ht : fields 5 = []) :
    RunsExactly computer.step (configuration .countMove initial (frontData [] tape fields))
      (configuration .groupZero initial (frontData (fields 3) tape fields))
      (2*(fields 3).length+2) := by
  have h := count_copy initial.2 (frontData [] tape fields).tapes rfl ht
  change RunsExactly computer.step _ (cfg Label.groupZero initial.2
    (Function.update (frontData [] tape fields).tapes counter (fields 3))) _ at h
  rw [front_update_counter] at h
  exact h

theorem zero_front (count tape : List Bool) (fields : Fin 6 → List Bool) :
    computer.step (configuration .groupZero initial (frontData count tape fields)) =
      some (configuration (.emitMove 0) initial (frontData count (false::tape) fields)) := by
  have h := zero_accumulator initial.2 (frontData count tape fields).tapes
  rw [front_random, front_update_random] at h
  exact h

theorem emit_headers (r m s g tape : List Bool) :
    RunsExactly computer.step
      (configuration .groupZero initial (frontData g tape (fieldWords r m s g [] [])))
      (configuration (.groups (Iteration.own Sampling.GroupBody.machine 0)) initial
        (frontData g (Sampling.GroupBody.word r m s [] tape) (fieldWords [] [] [] g [] [])))
      (2*(r.length+m.length+s.length)+10) := by
  have h0 := runsExactly_one (zero_front g tape (fieldWords r m s g [] []))
  have h1 := emit_front 0 g (false::tape) (fieldWords r m s g [] []) rfl
  have h2 := emit_front 1 g (Encoding.frame s ++ false::tape) (fieldWords r m [] g [] []) rfl
  have h3 := emit_front 2 g (Encoding.frame m ++ Encoding.frame s ++ false::tape)
    (fieldWords r [] [] g [] []) rfl
  simp only [fieldWords_update] at h1 h2 h3
  norm_num [Fin.ext_iff] at h1 h2 h3
  dsimp only [emitNext] at h1 h2 h3
  have h := ((h0.trans h1).trans h2).trans h3
  have e0 : fieldWords r [] [] g [] [] 0 = r := rfl
  have e1 : fieldWords r m [] g [] [] 1 = m := rfl
  have e2 : fieldWords r m s g [] [] 2 = s := rfl
  rw [e0, e1, e2] at h
  have ht : 2*r.length+3+(2*m.length+3+(2*s.length+3+1)) =
      2*(r.length+m.length+s.length)+10 := by omega
  rw [ht] at h
  dsimp only [FinTM2.step] at h ⊢
  have hz : Encoding.frame [] = [false] := rfl
  simpa only [Sampling.GroupBody.word, List.append_assoc, hz, List.singleton_append] using h

theorem prepare_groups (r m s g tape : List Bool) :
    RunsExactly computer.step
      (configuration (.scan 0) initial (frontData []
        (Encoding.frame r ++ Encoding.frame m ++ Encoding.frame s ++ Encoding.frame g ++ tape)
        (fieldWords [] [] [] [] [] [])))
      (configuration (.groups (Iteration.own Sampling.GroupBody.machine 0)) initial
        (frontData g (Sampling.GroupBody.word r m s [] tape) (fieldWords [] [] [] g [] [])))
      (4*(r.length+m.length+s.length+g.length)+20) := by
  have h := ((parse_headers r m s g tape).trans
    (copy_front tape (fieldWords r m s g [] []) rfl)).trans (emit_headers r m s g tape)
  have ht : (2*(r.length+m.length+s.length)+10)+
      ((2*(fieldWords r m s g [] [] 3).length+2)+
        (2*(r.length+m.length+s.length+g.length)+8)) =
      4*(r.length+m.length+s.length+g.length)+20 := by
    change (2*(r.length+m.length+s.length)+10)+
      ((2*g.length+2)+(2*(r.length+m.length+s.length+g.length)+8)) = _
    omega
  rw [ht] at h
  exact h

theorem input_front (word : List Bool) :
    initList computer word = configuration .dispatch initial
      (frontData [] word (fieldWords [] [] [] [] [] [])) := by
  rw [Machine.init_eq]
  congr 1
  funext j
  rcases j with (j | j) | (j | (j | j))
  · fin_cases j <;> rfl
  · by_cases hj : j = Sampling.GroupBody.random
    · subst j; rfl
    · have ho : (Sum.inl (Sum.inr j) : Stack) ≠ random := by
        intro h; exact hj (Sum.inr.inj (Sum.inl.inj h))
      exact (wordTape_other random _ word ho).trans
        (wordTape_other Sampling.GroupBody.random j word hj).symm
  · fin_cases j <;> rfl
  all_goals rfl

theorem dispatch_positive (r m s g tape : List Bool) :
    computer.step (initList computer (payload r m s g tape)) =
      some (configuration (.scan 0) initial
        (frontData [] (Encoding.frame r ++ (Encoding.frame m ++ (Encoding.frame s ++
          (Encoding.frame g ++ tape)))) (fieldWords [] [] [] [] [] []))) := by
  rw [input_front]
  change some (⟨some (Label.scan 0), initial,
    Function.update (frontData [] (payload r m s g tape) (fieldWords [] [] [] [] [] [])).tapes
      random (Encoding.frame r ++ (Encoding.frame m ++ (Encoding.frame s ++
        (Encoding.frame g ++ tape))))⟩ : computer.Cfg) = _
  rw [front_update_random]
  rfl

theorem prepare_payload (r m s g tape : List Bool) :
    RunsExactly computer.step (initList computer (payload r m s g tape))
      (configuration (.groups (Iteration.own Sampling.GroupBody.machine 0)) initial
        (frontData g (Sampling.GroupBody.word r m s [] tape) (fieldWords [] [] [] g [] [])))
      (4*(r.length+m.length+s.length+g.length)+21) := by
  have prep := prepare_groups r m s g tape
  simp only [List.append_assoc] at prep
  have h := (runsExactly_one (dispatch_positive r m s g tape)).trans prep
  dsimp only [FinTM2.step] at h ⊢
  simpa only [List.append_assoc, Nat.add_assoc] using h

end Counting.Algorithm.KarpLubyRequest.Evaluation
