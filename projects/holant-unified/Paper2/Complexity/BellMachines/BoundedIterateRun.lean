import Paper2.Complexity.BellMachines.BoundedIterate

namespace Paper2.Complexity.BellMachines.BoundedIterate
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines GraphPreprocessing
variable (m : Machine)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192

 theorem prepare (count word : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 0) (fun _ => []) (Paper2.Algebraic.frame count ++ word) [] [])
      (config m (.inr 2) (fun _ => []) word count []) (2*(count.length+1)) := by
  have h := Frame.extract_exact (inputKey m) (countKey m) (tempKey m)
    (by simp [inputKey,countKey]) (by simp [inputKey,tempKey]) (by simp [countKey,tempKey])
    (TM2.step (program m)) (.inr 0) (.inr 1) (.inr 2) (.inr 7)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] [] []) count word []
  simpa only [config,tapes3,update_input,update_count,update_temp,List.append_nil] using h

 theorem load_word (count word : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 2) (fun _ => []) word count [])
      (ready m (.inr 4) word count) (2*(word.length+1)) := by
  have h := MoveWord.move_exact (inputKey m) (.inl m.input : Stack m) (tempKey m)
    (by simp [inputKey]) (by simp [inputKey,tempKey]) (by simp [tempKey])
    (TM2.step (program m)) (.inr 2) (.inr 3) (.inr 4)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] count []) word []
  simpa only [ready,config,tapes3,update_input,update_source,update_temp,List.append_nil,
    wordTape,Function.update_eq_self] using h

 theorem counter_cons (word count : List Bool) :
    TM2.step (program m) (ready m (.inr 4) word (true::count)) =
      some (ready m (.inl m.main) word count) := by
  change some (cfg (.inl m.main : Label m) m.initial
    (Function.update (tapes m (wordTape m.input word) [] (true::count) []) (countKey m) count)) = _
  rw [update_count]
  rfl

 theorem counter_nil (word : List Bool) :
    TM2.step (program m) (ready m (.inr 4) word []) =
      some (ready m (.inr 7) word []) := by
  change some (cfg (.inr 7 : Label m) m.initial
    (Function.update (tapes m (wordTape m.input word) [] [] []) (countKey m) [])) = _
  rw [update_count]
  rfl

 theorem call (word result count : List Bool) (n : ℕ)
    (h : (fun c => c.bind m.computer.step)^[n] (some (initList m.computer word)) =
      some (haltList m.computer result)) :
    RunsExactly (TM2.step (program m))
      (ready m (.inl m.main) word count)
      (config m (.inr 5) (wordTape m.output result) [] count []) n := by
  have hh := Call.run (LeftMap.states m) Sum.inl (some (.inr (5 : Fin 8)))
    m.program (program m) (fun _ => rfl) (initList m.computer word)
    (haltList m.computer result) (extras [] count []) n h
  rw [Machine.init_eq,Machine.halt_eq] at hh
  exact hh

 theorem reload (hio : m.output ≠ m.input) (result count : List Bool) :
    RunsExactly (TM2.step (program m))
      (config m (.inr 5) (wordTape m.output result) [] count [])
      (ready m (.inr 4) result count) (2*(result.length+1)) := by
  have h := MoveWord.move_exact (.inl m.output : Stack m) (.inl m.input : Stack m) (tempKey m)
    (by simpa) (by simp [tempKey]) (by simp [tempKey])
    (TM2.step (program m)) (.inr 5) (.inr 6) (.inr 4)
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) m.initial
    (tapes m (fun _ => []) [] count []) result []
  have hempty : Function.update (Function.update (fun _ : m.K => []) m.output result) m.input [] =
      Function.update (fun _ : m.K => []) m.output result := by
    funext k
    by_cases hi : k = m.input
    · subst k; simp [Function.update,hio.symm]
    · simp [Function.update,hi]
  simpa only [ready,config,tapes3,update_source,update_temp,List.append_nil,
    wordTape,Function.update_eq_self,hempty] using h

 theorem final_halt (word : List Bool) :
    TM2.step (program m) (ready m (.inr 7) word []) =
      some (haltList (machine m).computer word) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,m.initial),tapes m (wordTape m.input word) [] [] []⟩ : (machine m).Config) = _
  congr 2
  funext k
  rcases k with k | k
  · simp [tapes,wordTape,machine,Function.comp_def]
  · fin_cases k <;> simp [tapes,extras,wordTape,machine]

end Paper2.Complexity.BellMachines.BoundedIterate
