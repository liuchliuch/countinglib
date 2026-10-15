import ComplexCSP.Structure.MaltsevTypeStackSimulation
import ComplexCSP.Complexity.WitnessEncoding

/-! # Typed materialized search and the literal raw continuation stack

The callback equations in the bridge are local representation laws. The actual
reconstruction and weighted-row programs discharge them; they are not relation
membership, type-partition, or evaluation oracles.
-/
namespace ComplexCSP.MaltsevTypeStack
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding
variable {A : Type*} [DecidableEq A] {d n : ℕ}

omit [DecidableEq A] in
theorem word_replaceCoordinate (target : Tuple (Fin d) n) (i : Fin n) (a : Fin d) :
    replaceAt (word target) i.val a.val = word (replaceCoordinate target i a) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hjn : j < n := by simpa using hj
    simp only [replaceAt, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    by_cases hji : j = i.val
    · subst j
      simp [word, replaceCoordinate]
    · have hfin : (⟨j,hjn⟩ : Fin n) ≠ i := by intro he; exact hji (congrArg Fin.val he)
      simp [hji, word, replaceCoordinate, view, Function.update_of_ne hfin]

/-- Child traversal preserves both exact last-occurrence deduplication order and
cache order. Only the separately counted transitions are erased. -/
theorem childFold_first_map (children : List (Fin d))
    (F : ℕ → ListTypeCache A → SearchResult A)
    (G : Fin d → ListTypeCache A → List A × ListTypeCache A)
    (hFG : ∀ a c, (F a.val c).1 = G a c) (state : SearchResult A) :
    (childFold (children.map Fin.val) F state).1 =
      children.foldl (fun s a => let next := G a s.2;
        ((s.1 ++ next.1).dedup,next.2)) state.1 := by
  induction children generalizing state with
  | nil => rfl
  | cons a children ih =>
    simp only [List.map_cons, childFold, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [hFG]

/-- The list reference machine computes precisely the existing materialized
prefix-type search, for the actual representation laws of its two callbacks. -/
theorem search_materialized (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A)
    (reconstructRaw : ℕ → List ℕ → Option (List ℕ)) (labelRaw : List ℕ → A)
    (hrec : ∀ len, len ≤ n → ∀ x, reconstructRaw len (word x) = (reconstructTo m W x len).map word)
    (hlab : ∀ x, labelRaw (word x) = label x)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n) (cache : ListTypeCache A) :
    (search n (List.range d) reconstructRaw labelRaw fuel len (word target) cache).1 =
      materializedTypeSearch m W label fuel len target cache := by
  induction fuel generalizing len target cache with
  | zero =>
    rw [search, materializedTypeSearch, hrec len (by omega)]
    cases hw : reconstructTo m W target len with
    | none => rfl
    | some w =>
      simp only [Option.map_some, hlab]
      cases hc : cachedTypeList cache len (label w) <;> rfl
  | succ fuel ih =>
    rw [search, materializedTypeSearch, hrec len (by omega)]
    cases hw : reconstructTo m W target len with
    | none => rfl
    | some w =>
      simp only [Option.map_some, hlab]
      cases hc : cachedTypeList cache len (label w) with
      | some S => rfl
      | none =>
        by_cases hlt : len < n
        · simp only [if_pos hlt, dif_pos hlt]
          have hf := childFold_first_map (List.finRange d)
            (fun a c => search n (List.range d) reconstructRaw labelRaw fuel (len+1)
              (replaceAt (word target) len a) c)
            (fun a c => materializedTypeSearch m W label fuel (len+1)
              (replaceCoordinate target ⟨len,hlt⟩ a) c)
            (fun a c => by
              rw [word_replaceCoordinate target ⟨len,hlt⟩ a]
              exact ih _ (by omega) _ _)
            (([],cache),0)
          have hrange : (List.finRange d).map Fin.val = List.range d := by simp
          rw [hrange] at hf
          exact congrArg (fun p : List A × ListTypeCache A => (p.1,(len,p.1)::p.2)) hf
        · simp only [if_neg hlt, dif_neg hlt]

/-- The concrete stack reaches the exact materialized output and cache. -/
theorem materialized_runs (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A)
    (reconstructRaw : ℕ → List ℕ → Option (List ℕ)) (labelRaw : List ℕ → A)
    (hrec : ∀ len, len ≤ n → ∀ x, reconstructRaw len (word x) = (reconstructTo m W x len).map word)
    (hlab : ∀ x, labelRaw (word x) = label x)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n)
    (cache : ListTypeCache A) (stack : List (Frame A)) :
    Runs (step n (List.range d) reconstructRaw labelRaw) (callState len (word target) stack cache)
      (returnState len (word target) (materializedTypeSearch m W label fuel len target cache).1
        stack (materializedTypeSearch m W label fuel len target cache).2)
      (search n (List.range d) reconstructRaw labelRaw fuel len (word target) cache).2 := by
  have h := search_runs n (List.range d) reconstructRaw labelRaw fuel len hdepth (word target) cache stack
  rw [show (search n (List.range d) reconstructRaw labelRaw fuel len (word target) cache).1 =
    materializedTypeSearch m W label fuel len target cache from
    search_materialized m W label reconstructRaw labelRaw hrec hlab fuel len hdepth target cache] at h
  exact h

/-- The halt test plus every successful control transition is bounded by twice
the already-proved cache/call potential. The class image is a proof bound only,
never an input alphabet or search oracle. -/
theorem materialized_transition_bound {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label)
    (reconstructRaw : ℕ → List ℕ → Option (List ℕ)) (labelRaw : List ℕ → A)
    (hrec : ∀ len, len ≤ n → ∀ x, reconstructRaw len (word x) = (reconstructTo m W x len).map word)
    (hlab : ∀ x, labelRaw (word x) = label x)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U) :
    (search n (List.range d) reconstructRaw labelRaw fuel len (word target) []).2 + 1 ≤
      2 * (1 + d * ((n + 1) * U.card)) := by
  have hc := search_cost_cache_bound n (List.range d) reconstructRaw labelRaw fuel len (word target) []
  rw [search_materialized m W label reconstructRaw labelRaw hrec hlab fuel len hdepth] at hc
  have he := congrArg (fun p : Finset A × TypeCache A => p.2.length)
    (materializedTypeSearch_erase m W label fuel len target [])
  simp only [eraseTypeResult, eraseTypeCache, List.length_map, List.map_nil] at he
  have hl := typeSearch_cache_length_le hm hR hW label hTP fuel len hdepth target U hU
  rw [← he] at hl
  simp only [List.length_range, List.length_nil, mul_zero, add_zero] at hc
  nlinarith

end ComplexCSP.MaltsevTypeStack
