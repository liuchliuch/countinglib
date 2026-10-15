import ComplexCSP.Complexity.SupportWitnessPrimitives
import ComplexCSP.Structure.MaltsevWitnessPinPrefix

/-! # Literal agreement of support-witness pinning machines -/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityProjectedClosure
variable {d n : ℕ}

/-- Materialize every actual lookup once, in coordinate/color order. -/
def encodeCode (W : Code (Fin d) n) : RawWitness :=
  (List.ofFn (fun i => List.ofFn (fun a => maybeWord (W.lookup i a))),maybeWord W.seed)

theorem encodeCode_store (W : Code (Fin d) n) :
    encodeCode W = (rawTable (storeCode W),maybeWord (storeCode W).seed) := by
  simp [encodeCode,rawTable,storeCode,Vector.toList_ofFn,List.map_ofFn,Function.comp_def]

theorem encodeCode_stored (W : StoredCode d n) :
    encodeCode W.toCode = (rawTable W,maybeWord W.seed) := by
  apply Prod.ext
  · apply List.ext_getElem
    · simp [encodeCode,rawTable]
    · intro i hi hi'
      simp only [encodeCode,List.getElem_ofFn,rawTable,List.getElem_map]
      apply List.ext_getElem
      · simp
      · intro a ha ha'
        simp [StoredCode.toCode]
  · rfl

@[simp] theorem tableLookup_encodeCode (W : Code (Fin d) n) (i : Fin n) (a : Fin d) :
    tableLookup (encodeCode W).1 i.val a.val = maybeWord (W.lookup i a) := by
  simp [tableLookup,encodeCode,List.getD_eq_getElem?_getD,i.isLt,a.isLt]

theorem storedRows_encodeCode (W : Code (Fin d) n) :
    storedRows (encodeCode W) = (MaltsevWitness.storedRows W).map word := by
  simp only [storedRows,encodeCode,MaltsevWitness.storedRows,maybeWord,List.map_append,
    List.map_flatten,List.map_ofFn,Function.comp_def,List.flatMap_def,
    List.flatten_flatten]

theorem first_map_word (xs : List (Tuple (Fin d) n)) :
    first (xs.map word) = maybeWord xs.head? := by cases xs <;> rfl

theorem forkTest_encodeCode (W : Code (Fin d) n) (i : Fin n) (a b : Fin d) :
    forkTest (encodeCode W,i.val,a.val,b.val) = MaltsevWitness.forkTest W i a b := by
  simp only [forkTest,tableLookup_encodeCode,MaltsevWitness.forkTest]
  cases hu : W.lookup i a with
  | none => simp [maybeWord]
  | some u =>
    cases hv : W.lookup i b with
    | none => simp [maybeWord]
    | some v =>
      simp only [maybeWord,Option.toList_some,List.map_singleton,List.cons_ne_self,
        List.headD_cons,↓reduceIte]
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq,PrefixEq] using prefixEqual_word i.val u v

theorem scopeWord_firstPair (i : Fin (n+1)) : scopeWord (firstPair i) = [0,i.val] := by
  simp [scopeWord,firstPair,List.ofFn_succ]

theorem pinCandidates_encodeCode (m : Operation (Fin d)) (W : Code (Fin d) (n+1))
    (a : Fin d) (i : Fin (n+1)) :
    pinCandidates d (fun x y z => m (x,y,z)) (encodeCode W,a.val,i.val) =
      (MaltsevWitness.pinCandidates m W a i).map word := by
  simp only [pinCandidates,storedRows_encodeCode,← scopeWord_firstPair i,projectedClosure_word,
    MaltsevWitness.pinCandidates,List.filter_map,Function.comp_def]
  congr 1
  apply List.filter_congr
  intro x _
  have hx := word_getD x (0 : Fin (n+1))
  simp only [Fin.val_zero] at hx
  rw [hx]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,beq_iff_eq]
  exact Fin.val_injective.eq_iff

theorem pinAnchor_encodeCode (m : Operation (Fin d)) (W : Code (Fin d) (n+1))
    (a : Fin d) (i : Fin (n+1)) (b : Fin d) :
    pinAnchor d (fun x y z => m (x,y,z)) (encodeCode W,a.val,i.val,b.val) =
      maybeWord (MaltsevWitness.pinAnchor m W a i b) := by
  simp only [pinAnchor,pinCandidates_encodeCode,List.filter_map,Function.comp_def]
  have h : ∀ x : Tuple (Fin d) (n+1), forkTest (encodeCode W,i.val,(word x).getD i.val 0,b.val) =
      MaltsevWitness.forkTest W i (view x i) b := by
    intro x
    rw [word_getD x i]
    exact forkTest_encodeCode W i _ b
  simp_rw [h]
  rw [first_map_word,List.head?_filter]
  rfl

theorem replaceAt_word (x : Tuple (Fin d) n) (i : Fin n) (a : Fin d) :
    MaltsevTypeStack.replaceAt (word x) i.val a.val = word (replaceCoordinate x i a) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hjn : j < n := by simpa using hj'
    by_cases he : j = i.val
    · subst j
      simp [MaltsevTypeStack.replaceAt,word,replaceCoordinate]
    · have he' : (⟨j,hjn⟩ : Fin n) ≠ i := fun h => he (congrArg Fin.val h)
      simp [MaltsevTypeStack.replaceAt,word,replaceCoordinate,view,he,he']

theorem transport_encodeCode (m : Operation (Fin d)) (W : Code (Fin d) n)
    (i : Fin n) (a : Fin d) (x : Tuple (Fin d) n) :
    transport d (fun x y z => m (x,y,z)) (encodeCode W,i.val,a.val,word x) =
      maybeWord (MaltsevWitness.transportCode m W i x a) := by
  rw [transport,replaceAt_word,encodeCode_store]
  simpa only [storeCode_toCode,MaltsevWitness.transportCode] using
    repairWord_stored m (storeCode W) i (replaceCoordinate x i a) x

theorem pinPositiveLookup_encodeCode (m : Operation (Fin d)) (W : Code (Fin d) (n+1))
    (a : Fin d) (i : Fin (n+1)) (b : Fin d) (hi : i.val ≠ 0) :
    pinPositiveLookup d (fun x y z => m (x,y,z)) (encodeCode W,a.val,i.val,b.val) =
      maybeWord ((pinFirstCode m W a).lookup i b) := by
  rw [pinPositiveLookup,pinAnchor_encodeCode]
  simp only [pinFirstCode,if_neg hi]
  cases h : MaltsevWitness.pinAnchor m W a i b with
  | none => simp [maybeWord]
  | some z =>
    simp only [maybeWord,Option.toList_some,List.map_singleton,List.cons_ne_self,
      List.headD_cons,↓reduceIte,Option.bind_some]
    exact transport_encodeCode m W i b z

@[simp] theorem encodeCode_table_length (W : Code (Fin d) n) : (encodeCode W).1.length = n := by
  simp [encodeCode]

theorem tailTuple_word (x : Tuple (Fin d) (n+1)) :
    (word x).tail = word (tailTuple x) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [word,tailTuple,view]

theorem tailMaybe_word (x : Option (Tuple (Fin d) (n+1))) :
    (maybeWord x).map List.tail = maybeWord (x.map tailTuple) := by
  cases x with
  | none => rfl
  | some x => simp only [maybeWord,Option.toList_some,Option.map_some,List.map_singleton,tailTuple_word]

private theorem map_range_eq_ofFn {A : Type} (f : ℕ → A) (n : ℕ) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

/-- Pin/drop agrees with the entire typed materialized table and seed, including
its exact first-anchor choices. No relational correctness assumption is needed. -/
theorem pinDrop_encodeCode (m : Operation (Fin d)) (W : Code (Fin d) (n+1)) (a : Fin d) :
    pinDrop d (fun x y z => m (x,y,z)) (encodeCode W,a.val) =
      encodeCode (pinDropCode m W a) := by
  apply Prod.ext
  · change ((List.range (encodeCode W).1.tail.length).map (fun i =>
      (List.range d).map (fun b => (pinPositiveLookup d (fun x y z => m (x,y,z))
        (encodeCode W,a.val,i+1,b)).map List.tail))) = _
    rw [List.length_tail,encodeCode_table_length,Nat.add_sub_cancel,map_range_eq_ofFn]
    change List.ofFn _ = List.ofFn _
    congr 1
    funext i
    rw [map_range_eq_ofFn]
    congr 1
    funext b
    have hpos := pinPositiveLookup_encodeCode m W a i.succ b (by simp)
    simp only [Fin.val_succ] at hpos
    rw [hpos,tailMaybe_word]
    rfl
  · change (tableLookup (encodeCode W).1 0 a.val).map List.tail = _
    have hzero := tableLookup_encodeCode W (0 : Fin (n+1)) a
    simp only [Fin.val_zero] at hzero
    rw [hzero,tailMaybe_word]
    rfl

end ComplexCSP.ComplexitySupportWitnessPrimitives
