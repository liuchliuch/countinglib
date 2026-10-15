import ComplexCSP.Structure.MaltsevTypeStackStored
import ComplexCSP.Structure.MaltsevTypeStackBounds

/-! # Bounds for every intermediate state of the actual stored-witness stack -/
namespace ComplexCSP.MaltsevTypeStack
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding
variable {A : Type*} [DecidableEq A] {d n : ℕ}

/-- All changing control data are finite words, bounded prefix lengths and
present labels. No runtime enumeration of U is supplied to the machine. -/
def StateValid (d n : ℕ) (U : Finset A) (s : State A) : Prop :=
  DepthValid n s ∧ WordsValid d n (List.range d) s ∧ LabelsValid U s ∧ CacheLevelsValid n s

omit [DecidableEq A] in
/-- The label callback is used only on actual support witnesses produced by the
proved reconstruction algorithm. -/
theorem storedReconstruct_label_mem {m : Operation (Fin d)} {W : StoredCode d n}
    {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W.toCode R)
    (label : Tuple (Fin d) n → A) (labelRaw : List ℕ → A)
    (hlab : ∀ x, labelRaw (word x) = label x)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U)
    {len : ℕ} (hlen : len ≤ n) {target w : List ℕ} (htarget : WordValid d n target)
    (hw : storedReconstruct m W len target = some w) : labelRaw w ∈ U := by
  obtain ⟨x,rfl⟩ := htarget
  rw [storedReconstruct_word m W len hlen] at hw
  obtain ⟨y,hy,rfl⟩ := Option.map_eq_some_iff.mp hw
  rw [hlab]
  have hs := reconstructTo_sound hR hW x len hy
  simpa only [ofFn_view] using hU (view y) hs

/-- One actual transition preserves every size-relevant data invariant. -/
theorem stored_step_valid {m : Operation (Fin d)} {W : StoredCode d n}
    {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W.toCode R)
    (label : Tuple (Fin d) n → A) (labelRaw : List ℕ → A)
    (hlab : ∀ x, labelRaw (word x) = label x)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U)
    {s t : State A} (hs : StateValid d n U s)
    (he : step n (List.range d) (storedReconstruct m W) labelRaw s = some t) : StateValid d n U t := by
  refine ⟨step_depthValid _ _ _ _ hs.1 he,
    step_wordsValid d n (List.range d) (by intro a ha; exact List.mem_range.mp ha) _ _ hs.1 hs.2.1 he,
    step_labelsValid _ _ _ _ hs.2.2.1 ?_ he,
    step_cacheLevelsValid _ _ _ _ hs.1 hs.2.2.2 he⟩
  intro w hw
  exact storedReconstruct_label_mem hR hW label labelRaw hlab U hU hs.1.1 hs.2.1.1 hw

/-- Every prefix of a genuine finite execution retains those invariants. -/
theorem stored_runs_valid {m : Operation (Fin d)} {W : StoredCode d n}
    {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W.toCode R)
    (label : Tuple (Fin d) n → A) (labelRaw : List ℕ → A)
    (hlab : ∀ x, labelRaw (word x) = label x)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U)
    {s t : State A} {k : ℕ} (hr : Runs (step n (List.range d) (storedReconstruct m W) labelRaw) s t k)
    (hs : StateValid d n U s) : StateValid d n U t := by
  induction hr with
  | refl => exact hs
  | step he _ ih => exact ih (stored_step_valid hR hW label labelRaw hlab U hU hs he)

omit [DecidableEq A] in
theorem initial_state_valid (U : Finset A) (len : ℕ) (hlen : len ≤ n) (x : Tuple (Fin d) n) :
    StateValid d n U (callState len (word x) [] []) := by
  exact ⟨⟨hlen,True.intro⟩,⟨wordValid_word x,by simp [callState]⟩,
    ⟨labelList_nil U,by simp [callState],by simp [callState]⟩,by simp [CacheLevelsValid,callState]⟩

/-- A compact package of literal record/list sizes, for the bit-code compiler.
The label bit lengths are separately supplied by the proved marginal bound. -/
theorem stateValid_sizes {U : Finset A} {s : State A} (hs : StateValid d n U s) :
    s.currentLen ≤ n ∧ s.currentTarget.length = n ∧ s.stack.length ≤ n ∧
    s.returnedLabels.length ≤ U.card ∧
    (∀ f ∈ s.stack, f.parentTarget.length = n ∧ f.remainingColors.length ≤ d ∧
      f.accumulatedLabels.length ≤ U.card) ∧
    (∀ e ∈ s.cache, e.1 ≤ n ∧ e.2.length ≤ U.card) := by
  refine ⟨hs.1.1,hs.2.1.1.length,hs.1.stack_length,hs.2.2.1.1.length_le,?_,?_⟩
  · intro f hf
    obtain ⟨hw,hc⟩ := hs.2.1.2 f hf
    exact ⟨hw.length,by simpa using hc.length_le,(hs.2.2.1.2.1 f hf).length_le⟩
  · intro e he
    exact ⟨hs.2.2.2 e he,(hs.2.2.1.2.2 e he).length_le⟩

/-- For every reached state, the frame and label bounds hold and cache records
are at most the number of elapsed successful transitions. -/
theorem stored_reached_sizes {m : Operation (Fin d)} {W : StoredCode d n}
    {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W.toCode R)
    (label : Tuple (Fin d) n → A) (labelRaw : List ℕ → A)
    (hlab : ∀ x, labelRaw (word x) = label x)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U)
    (len : ℕ) (hlen : len ≤ n) (target : Tuple (Fin d) n)
    {s : State A} {k : ℕ}
    (hr : Runs (step n (List.range d) (storedReconstruct m W) labelRaw)
      (callState len (word target) [] []) s k) :
    StateValid d n U s ∧ s.cache.length ≤ k := by
  refine ⟨stored_runs_valid hR hW label labelRaw hlab U hU hr (initial_state_valid U len hlen target),?_⟩
  simpa [callState] using hr.cache_length

end ComplexCSP.MaltsevTypeStack
