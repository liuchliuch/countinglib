import ComplexCSP.Structure.MaltsevTypeCost

/-!
# List-backed executable type search

No Finset.toList or classical enumeration is used. The erasure theorem connects
the actual materialized label lists/cache to the proved finite-set algorithm.
-/
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ} {A : Type*} [DecidableEq A]

@[simp] theorem dedup_toFinset (xs : List A) : xs.dedup.toFinset = xs.toFinset := by
  ext a
  simp

abbrev ListTypeCache (A : Type*) := List (ℕ × List A)

def eraseTypeCache (cache : ListTypeCache A) : TypeCache A :=
  cache.map (fun e => (e.1, e.2.toFinset))

def eraseTypeResult (result : List A × ListTypeCache A) : Finset A × TypeCache A :=
  (result.1.toFinset, eraseTypeCache result.2)

def cachedTypeList (cache : ListTypeCache A) (len : ℕ) (a : A) : Option (List A) :=
  (cache.find? (fun e => decide (e.1 = len ∧ a ∈ e.2))).map Prod.snd

@[simp] theorem cachedTypeList_erase (cache : ListTypeCache A) (len : ℕ) (a : A) :
    (cachedTypeList cache len a).map List.toFinset = cachedType (eraseTypeCache cache) len a := by
  simp [cachedTypeList, cachedType, eraseTypeCache, List.find?_map, Function.comp_def, Option.map_map]

def materializedTypeSearch (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) :
    ℕ → ℕ → Tuple (Fin d) n → ListTypeCache A → List A × ListTypeCache A
  | fuel, len, target, cache =>
    match reconstructTo m W target len with
    | none => ([], cache)
    | some w =>
      match cachedTypeList cache len (label w) with
      | some S => (S.dedup, cache)
      | none =>
        match fuel with
        | 0 => ([label w], (len, [label w]) :: cache)
        | fuel + 1 =>
          if h : len < n then
            let result := (List.finRange d).foldl (fun state a =>
              let next := materializedTypeSearch m W label fuel (len + 1)
                (replaceCoordinate target ⟨len, h⟩ a) state.2
              ((state.1 ++ next.1).dedup, next.2)) ([], cache)
            (result.1, (len, result.1) :: result.2)
          else ([label w], (len, [label w]) :: cache)

theorem fold_type_erasure (children : List (Fin d))
    (F : Fin d → ListTypeCache A → List A × ListTypeCache A)
    (G : Fin d → TypeCache A → Finset A × TypeCache A)
    (hFG : ∀ a c, eraseTypeResult (F a c) = G a (eraseTypeCache c))
    (state : List A × ListTypeCache A) :
    eraseTypeResult (children.foldl (fun state a =>
      let next := F a state.2; ((state.1 ++ next.1).dedup, next.2)) state) =
      children.foldl (fun state a => let next := G a state.2;
        (state.1 ∪ next.1, next.2)) (eraseTypeResult state) := by
  induction children generalizing state with
  | nil => rfl
  | cons a children ih =>
    rw [List.foldl_cons, List.foldl_cons, ih]
    congr 1
    have h := hFG a state.2
    simp only [eraseTypeResult, dedup_toFinset, List.toFinset_append] at h ⊢
    rw [← h]

theorem materializedTypeSearch_erase (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (fuel len : ℕ) (target : Tuple (Fin d) n) (cache : ListTypeCache A) :
    eraseTypeResult (materializedTypeSearch m W label fuel len target cache) =
      typeSearch m W label fuel len target (eraseTypeCache cache) := by
  induction fuel generalizing len target cache with
  | zero =>
    rw [materializedTypeSearch, typeSearch]
    cases hw : reconstructTo m W target len with
    | none => rfl
    | some w =>
      simp only []
      have ht := cachedTypeList_erase cache len (label w)
      cases hc : cachedTypeList cache len (label w) with
      | none =>
        simp only [hc, Option.map_none] at ht
        rw [← ht]
        simp [eraseTypeResult, eraseTypeCache]
      | some S =>
        simp only [hc, Option.map_some] at ht
        rw [← ht]
        simp [eraseTypeResult]
  | succ fuel ih =>
    rw [materializedTypeSearch, typeSearch]
    cases hw : reconstructTo m W target len with
    | none => rfl
    | some w =>
      simp only []
      have ht := cachedTypeList_erase cache len (label w)
      cases hc : cachedTypeList cache len (label w) with
      | some S =>
        simp only [hc, Option.map_some] at ht
        rw [← ht]
        simp [eraseTypeResult]
      | none =>
        simp only [hc, Option.map_none] at ht
        rw [← ht]
        by_cases hlt : len < n
        · simp only [dif_pos hlt]
          have hf := fold_type_erasure (List.finRange d)
            (fun a c => materializedTypeSearch m W label fuel (len + 1) (replaceCoordinate target ⟨len, hlt⟩ a) c)
            (fun a c => typeSearch m W label fuel (len + 1) (replaceCoordinate target ⟨len, hlt⟩ a) c)
            (fun a c => ih _ _ _) ([], cache)
          exact congrArg (fun p : Finset A × TypeCache A => (p.1, (len, p.1) :: p.2)) hf
        · simp only [dif_neg hlt]
          simp [eraseTypeResult, eraseTypeCache]

theorem fold_type_nodup (children : List (Fin d))
    (F : Fin d → ListTypeCache A → List A × ListTypeCache A)
    (state : List A × ListTypeCache A) (hstate : state.1.Nodup) :
    (children.foldl (fun state a =>
      let next := F a state.2; ((state.1 ++ next.1).dedup, next.2)) state).1.Nodup := by
  induction children generalizing state with
  | nil => exact hstate
  | cons a children ih => exact ih _ (List.nodup_dedup _)

theorem materializedTypeSearch_nodup (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (fuel len : ℕ) (target : Tuple (Fin d) n) (cache : ListTypeCache A) :
    (materializedTypeSearch m W label fuel len target cache).1.Nodup := by
  rw [materializedTypeSearch]
  cases hw : reconstructTo m W target len with
  | none => simp
  | some w =>
    simp only []
    cases hc : cachedTypeList cache len (label w) with
    | some S => exact List.nodup_dedup _
    | none =>
      cases fuel with
      | zero => simp
      | succ fuel =>
        by_cases hlt : len < n
        · simp only [dif_pos hlt]
          exact fold_type_nodup _ _ ([], cache) (by simp)
        · simp [hlt]

/-- Exact enumeration of the requested type as a duplicate-free runtime list. -/
theorem materializedTypeSearch_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n) (a : A) :
    a ∈ (materializedTypeSearch m W label fuel len target []).1 ↔ HasType R label len target a := by
  have he := materializedTypeSearch_erase m W label fuel len target []
  have hv : CacheValid R label ([] : TypeCache A) := by intro e he; simp at he
  have ht := (typeSearch_correct hm hR hW label hTP fuel len hdepth target [] hv).1 a
  have he' : (materializedTypeSearch m W label fuel len target []).1.toFinset =
      (typeSearch m W label fuel len target []).1 := congrArg Prod.fst he
  rw [← he'] at ht
  simpa only [List.mem_toFinset] using ht

/-- Runtime list length is bounded by the actual label image, rather than by
an externally supplied class enumeration. -/
theorem materializedTypeSearch_length_le {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U) :
    (materializedTypeSearch m W label fuel len target []).1.length ≤ U.card := by
  let output := (materializedTypeSearch m W label fuel len target []).1
  have hn : output.Nodup := materializedTypeSearch_nodup _ _ _ _ _ _ _
  have hs : output.toFinset ⊆ U := by
    intro a ha
    obtain ⟨x, hx, _, hxa⟩ := (materializedTypeSearch_correct hm hR hW label hTP fuel len hdepth target a).mp
      (List.mem_toFinset.mp ha)
    exact hxa ▸ hU x hx
  simpa [List.toFinset_card_of_nodup hn] using Finset.card_le_card hs

end ComplexCSP.MaltsevWitness
