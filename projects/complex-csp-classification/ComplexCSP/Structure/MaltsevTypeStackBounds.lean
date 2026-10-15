import ComplexCSP.Structure.MaltsevTypeStackCorrespondence

/-! # Structural invariants of every literal continuation transition

The depth and label invariants are proved for the actual transition relation.
In particular partial child unions are genuinely duplicate-free sublists of the
present class alphabet; no exponentially large row set is materialized.
-/
namespace ComplexCSP.MaltsevTypeStack
open MaltsevWitness ComplexityWitnessEncoding
variable {A : Type*} [DecidableEq A]

/-- Parent lengths strictly decrease down the continuation stack. -/
def DepthChain : ℕ → List (Frame A) → Prop
  | _, [] => True
  | ceiling, f :: rest => f.parentLen < ceiling ∧ DepthChain f.parentLen rest

omit [DecidableEq A] in
theorem DepthChain.length_le {ceiling : ℕ} {stack : List (Frame A)}
    (h : DepthChain ceiling stack) : stack.length ≤ ceiling := by
  induction stack generalizing ceiling with
  | nil => simp
  | cons f rest ih =>
    obtain ⟨hf,hr⟩ := h
    have hh := ih hr
    simp only [List.length_cons]
    omega

omit [DecidableEq A] in
theorem DepthChain.mem_lt {ceiling : ℕ} {stack : List (Frame A)}
    (h : DepthChain ceiling stack) {f : Frame A} (hf : f ∈ stack) : f.parentLen < ceiling := by
  induction stack generalizing ceiling with
  | nil => simp at hf
  | cons g rest ih =>
    rcases List.mem_cons.mp hf with rfl | hf
    · exact h.1
    · exact (ih h.2 hf).trans h.1

/-- The dimension bounds both the active prefix and all ancestor prefixes. -/
def DepthValid (dimension : ℕ) (s : State A) : Prop :=
  s.currentLen ≤ dimension ∧ DepthChain s.currentLen s.stack

/-- A successful transition cannot exceed the original dimension or grow a
stack deeper than the current prefix. -/
theorem step_depthValid (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    {s t : State A} (hs : DepthValid dimension s)
    (he : step dimension colors reconstruct label s = some t) : DepthValid dimension t := by
  rcases s with ⟨returning,len,target,returned,stack,cache⟩
  rcases hs with ⟨hlen,hchain⟩
  cases returning with
  | false =>
    simp only [step, Bool.false_eq_true, ↓reduceIte] at he
    cases hw : reconstruct len target with
    | none => simp only [hw] at he; cases he; exact ⟨hlen,hchain⟩
    | some w =>
      simp only [hw] at he
      cases hc : cachedTypeList cache len (label w) with
      | some labels => simp only [hc] at he; cases he; exact ⟨hlen,hchain⟩
      | none =>
        simp only [hc] at he
        by_cases hlt : len < dimension
        · simp only [if_pos hlt] at he
          cases colors with
          | nil => cases he; exact ⟨hlen,hchain⟩
          | cons a rest =>
            cases he
            exact ⟨by dsimp [callState]; omega, by simpa [callState,DepthChain] using And.intro (Nat.lt_succ_self len) hchain⟩
        · simp only [if_neg hlt] at he; cases he; exact ⟨hlen,hchain⟩
  | true =>
    cases stack with
    | nil => simp [step] at he
    | cons f rest =>
      obtain ⟨hparent,hrest⟩ := hchain
      simp only [step, ↓reduceIte] at he
      cases hc : f.remainingColors with
      | nil =>
        simp only [hc] at he
        cases he
        exact ⟨by dsimp [returnState]; omega,hrest⟩
      | cons a tail =>
        simp only [hc] at he
        cases he
        exact ⟨by dsimp [callState]; omega, by simpa [callState,DepthChain] using And.intro (Nat.lt_succ_self f.parentLen) hrest⟩

/-- Every state on any finite execution has at most dimension many frames. -/
theorem Runs.depthValid {dimension : ℕ} {colors : List ℕ}
    {reconstruct : ℕ → List ℕ → Option (List ℕ)} {label : List ℕ → A}
    {s t : State A} {k : ℕ} (hr : Runs (MaltsevTypeStack.step dimension colors reconstruct label) s t k)
    (hs : DepthValid dimension s) : DepthValid dimension t := by
  induction hr with
  | refl => exact hs
  | step he _ ih => exact ih (step_depthValid dimension colors reconstruct label hs he)

omit [DecidableEq A] in
theorem DepthValid.stack_length {dimension : ℕ} {s : State A} (hs : DepthValid dimension s) :
    s.stack.length ≤ dimension := (DepthChain.length_le hs.2).trans hs.1

/-- Present labels in a runtime list, with the literal no-duplicate invariant. -/
def LabelList (U : Finset A) (xs : List A) : Prop := xs.Nodup ∧ ∀ a ∈ xs, a ∈ U

omit [DecidableEq A] in
@[simp] theorem labelList_nil (U : Finset A) : LabelList U [] := by simp [LabelList]
omit [DecidableEq A] in
theorem labelList_singleton {U : Finset A} {a : A} (ha : a ∈ U) : LabelList U [a] := by
  simp [LabelList,ha]
theorem LabelList.dedup {U : Finset A} {xs : List A} (h : LabelList U xs) : LabelList U xs.dedup := by
  exact ⟨List.nodup_dedup _,fun a ha => h.2 a (List.mem_dedup.mp ha)⟩
theorem LabelList.union {U : Finset A} {xs ys : List A} (hx : LabelList U xs) (hy : LabelList U ys) :
    LabelList U (xs ++ ys).dedup := by
  refine ⟨List.nodup_dedup _,?_⟩
  intro a ha
  rcases List.mem_append.mp (List.mem_dedup.mp ha) with h | h
  · exact hx.2 a h
  · exact hy.2 a h

theorem LabelList.length_le {U : Finset A} {xs : List A} (h : LabelList U xs) : xs.length ≤ U.card := by
  have he : xs.toFinset ⊆ U := by intro a ha; exact h.2 a (List.mem_toFinset.mp ha)
  simpa [List.toFinset_card_of_nodup h.1] using Finset.card_le_card he

/-- Every returned list, partial child union, and cached list has actual present
labels. Cache length is bounded separately by transition count/cache semantics. -/
def LabelsValid (U : Finset A) (s : State A) : Prop :=
  LabelList U s.returnedLabels ∧
  (∀ f ∈ s.stack, LabelList U f.accumulatedLabels) ∧
  (∀ e ∈ s.cache, LabelList U e.2)

theorem cachedTypeList_labelList {U : Finset A} {cache : ListTypeCache A}
    (hc : ∀ e ∈ cache, LabelList U e.2) {len : ℕ} {a : A} {labels : List A}
    (he : cachedTypeList cache len a = some labels) : LabelList U labels := by
  unfold cachedTypeList at he
  obtain ⟨e,he,heq⟩ := Option.map_eq_some_iff.mp he
  have hm := List.mem_of_find?_eq_some he
  subst labels
  exact hc e hm

/-- Label preservation needs only the actual callback's support-range fact for
this one active input; no oracle for types or classes is assumed. -/
theorem step_labelsValid (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    {U : Finset A} {s t : State A} (hs : LabelsValid U s)
    (hlabel : ∀ w, reconstruct s.currentLen s.currentTarget = some w → label w ∈ U)
    (he : step dimension colors reconstruct label s = some t) : LabelsValid U t := by
  rcases s with ⟨returning,len,target,returned,stack,cache⟩
  rcases hs with ⟨hret,hstack,hcache⟩
  cases returning with
  | false =>
    simp only [step, Bool.false_eq_true, ↓reduceIte] at he
    cases hw : reconstruct len target with
    | none =>
      simp only [hw] at he
      cases he
      exact ⟨labelList_nil _,hstack,hcache⟩
    | some w =>
      have hl : LabelList U [label w] := labelList_singleton (hlabel w hw)
      simp only [hw] at he
      cases hc : cachedTypeList cache len (label w) with
      | some labels =>
        simp only [hc] at he
        cases he
        exact ⟨(cachedTypeList_labelList hcache hc).dedup,hstack,hcache⟩
      | none =>
        simp only [hc] at he
        by_cases hlt : len < dimension
        · simp only [if_pos hlt] at he
          cases colors with
          | nil =>
            cases he
            refine ⟨labelList_nil _,hstack,?_⟩
            intro e he
            rcases List.mem_cons.mp he with rfl | he
            · exact labelList_nil _
            · exact hcache e he
          | cons a rest =>
            cases he
            refine ⟨labelList_nil _,?_,hcache⟩
            intro f hf
            rcases List.mem_cons.mp hf with rfl | hf
            · exact labelList_nil _
            · exact hstack f hf
        · simp only [if_neg hlt] at he
          cases he
          refine ⟨hl,hstack,?_⟩
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hl
          · exact hcache e he
  | true =>
    cases stack with
    | nil => simp [step] at he
    | cons f rest =>
      have hf := hstack f (List.mem_cons_self ..)
      have hc := hf.union hret
      have hr : ∀ f ∈ rest, LabelList U f.accumulatedLabels := fun g hg => hstack g (List.mem_cons_of_mem _ hg)
      simp only [step, ↓reduceIte] at he
      cases hcolors : f.remainingColors with
      | nil =>
        simp only [hcolors] at he
        cases he
        refine ⟨hc,hr,?_⟩
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact hc
        · exact hcache e he
      | cons a tail =>
        simp only [hcolors] at he
        cases he
        refine ⟨labelList_nil _,?_,hcache⟩
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hc
        · exact hr g hg

/-- A word is a literal finite-domain tuple, including dimension zero. -/
def WordValid (d n : ℕ) (word : List ℕ) : Prop := ∃ x : Tuple (Fin d) n, ComplexityWitnessEncoding.word x = word

omit [DecidableEq A] in
theorem wordValid_word {d n : ℕ} (x : Tuple (Fin d) n) : WordValid d n (word x) := ⟨x,rfl⟩
omit [DecidableEq A] in
theorem WordValid.length {d n : ℕ} {xs : List ℕ} (h : WordValid d n xs) : xs.length = n := by
  obtain ⟨x,rfl⟩ := h
  exact word_length x
omit [DecidableEq A] in
theorem WordValid.replace {d n : ℕ} {xs : List ℕ} (h : WordValid d n xs)
    {i a : ℕ} (hi : i < n) (ha : a < d) : WordValid d n (replaceAt xs i a) := by
  obtain ⟨x,rfl⟩ := h
  refine ⟨replaceCoordinate x ⟨i,hi⟩ ⟨a,ha⟩,?_⟩
  exact (word_replaceCoordinate x ⟨i,hi⟩ ⟨a,ha⟩).symm

/-- Pending colors retain their exact order as a sublist of the fixed domain. -/
def WordsValid (d n : ℕ) (colors : List ℕ) (s : State A) : Prop :=
  WordValid d n s.currentTarget ∧
  ∀ f ∈ s.stack, WordValid d n f.parentTarget ∧ f.remainingColors.Sublist colors

/-- All target updates preserve both materialized length and the finite domain. -/
theorem step_wordsValid (d dimension : ℕ) (colors : List ℕ)
    (hcolors : ∀ a ∈ colors, a < d)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    {s t : State A} (hd : DepthValid dimension s) (hs : WordsValid d dimension colors s)
    (he : step dimension colors reconstruct label s = some t) : WordsValid d dimension colors t := by
  rcases s with ⟨returning,len,target,returned,stack,cache⟩
  rcases hs with ⟨htarget,hstack⟩
  rcases hd with ⟨hlen,hchain⟩
  cases returning with
  | false =>
    simp only [step, Bool.false_eq_true, ↓reduceIte] at he
    cases hw : reconstruct len target with
    | none => simp only [hw] at he; cases he; exact ⟨htarget,hstack⟩
    | some w =>
      simp only [hw] at he
      cases hc : cachedTypeList cache len (label w) with
      | some labels => simp only [hc] at he; cases he; exact ⟨htarget,hstack⟩
      | none =>
        simp only [hc] at he
        by_cases hlt : len < dimension
        · simp only [if_pos hlt] at he
          cases colors with
          | nil => cases he; exact ⟨htarget,hstack⟩
          | cons a rest =>
            cases he
            refine ⟨htarget.replace hlt (hcolors a (List.mem_cons_self ..)),?_⟩
            intro f hf
            rcases List.mem_cons.mp hf with rfl | hf
            · exact ⟨htarget,List.sublist_cons_self _ _⟩
            · exact hstack f hf
        · simp only [if_neg hlt] at he; cases he; exact ⟨htarget,hstack⟩
  | true =>
    cases stack with
    | nil => simp [step] at he
    | cons f rest =>
      obtain ⟨hp,hr⟩ := hchain
      obtain ⟨ht,hcs⟩ := hstack f (List.mem_cons_self ..)
      have hrest := fun g hg => hstack g (List.mem_cons_of_mem f hg)
      simp only [step, ↓reduceIte] at he
      cases hc : f.remainingColors with
      | nil => simp only [hc] at he; cases he; exact ⟨ht,hrest⟩
      | cons a tail =>
        have ha : a < d := hcolors a (hcs.subset (by simp [hc]))
        have htcs : tail.Sublist colors := (List.sublist_cons_self a tail).trans (hc ▸ hcs)
        simp only [hc] at he
        cases he
        refine ⟨ht.replace (by omega) ha,?_⟩
        intro g hg
        rcases List.mem_cons.mp hg with rfl | hg
        · exact ⟨ht,htcs⟩
        · exact hrest g hg

/-- Cache levels also use bounded unary prefix lengths. -/
def CacheLevelsValid (dimension : ℕ) (s : State A) : Prop := ∀ e ∈ s.cache, e.1 ≤ dimension

theorem step_cacheLevelsValid (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    {s t : State A} (hd : DepthValid dimension s) (hs : CacheLevelsValid dimension s)
    (he : step dimension colors reconstruct label s = some t) : CacheLevelsValid dimension t := by
  rcases s with ⟨returning,len,target,returned,stack,cache⟩
  rcases hd with ⟨hlen,hchain⟩
  cases returning with
  | false =>
    simp only [step, Bool.false_eq_true, ↓reduceIte] at he
    cases hw : reconstruct len target with
    | none => simp only [hw] at he; cases he; exact hs
    | some w =>
      simp only [hw] at he
      cases hc : cachedTypeList cache len (label w) with
      | some labels => simp only [hc] at he; cases he; exact hs
      | none =>
        simp only [hc] at he
        have hcons : ∀ labels, ∀ e ∈ (len,labels)::cache, e.1 ≤ dimension := by
          intro labels e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hlen
          · exact hs e he
        by_cases hlt : len < dimension
        · simp only [if_pos hlt] at he
          cases colors with
          | nil => cases he; exact hcons []
          | cons a rest => cases he; exact hs
        · simp only [if_neg hlt] at he; cases he; exact hcons _
  | true =>
    cases stack with
    | nil => simp [step] at he
    | cons f rest =>
      obtain ⟨hp,hr⟩ := hchain
      simp only [step, ↓reduceIte] at he
      cases hc : f.remainingColors with
      | nil =>
        simp only [hc] at he
        cases he
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · dsimp; omega
        · exact hs e he
      | cons a tail => simp only [hc] at he; cases he; exact hs

/-- One literal transition appends at most one cache record. -/
theorem step_cache_length (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    {s t : State A} (he : step dimension colors reconstruct label s = some t) :
    t.cache.length ≤ s.cache.length + 1 := by
  rcases s with ⟨returning,len,target,returned,stack,cache⟩
  cases returning with
  | false =>
    simp only [step, Bool.false_eq_true, ↓reduceIte] at he
    cases hw : reconstruct len target with
    | none => simp only [hw] at he; cases he; simp [returnState]
    | some w =>
      simp only [hw] at he
      cases hc : cachedTypeList cache len (label w) with
      | some labels => simp only [hc] at he; cases he; simp [returnState]
      | none =>
        simp only [hc] at he
        by_cases hlt : len < dimension
        · simp only [if_pos hlt] at he
          cases colors <;> cases he <;> simp [callState,returnState]
        · simp only [if_neg hlt] at he; cases he; simp [returnState]
  | true =>
    cases stack with
    | nil => simp [step] at he
    | cons f rest =>
      simp only [step, ↓reduceIte] at he
      cases hc : f.remainingColors <;> simp only [hc] at he <;> cases he <;> simp [callState,returnState]

theorem Runs.cache_length {dimension : ℕ} {colors : List ℕ}
    {reconstruct : ℕ → List ℕ → Option (List ℕ)} {label : List ℕ → A}
    {s t : State A} {k : ℕ} (hr : Runs (MaltsevTypeStack.step dimension colors reconstruct label) s t k) :
    t.cache.length ≤ s.cache.length + k := by
  induction hr with
  | refl => simp
  | step he _ ih =>
    have hs := step_cache_length dimension colors reconstruct label he
    omega

end ComplexCSP.MaltsevTypeStack

