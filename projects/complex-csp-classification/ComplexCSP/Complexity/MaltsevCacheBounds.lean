import ComplexCSP.Structure.MaltsevTypeMaterialized
import ComplexCSP.Complexity.EncodingBounds
import PlanarHom.GraphParallelCode

/-! # Bounds on actual list-backed type-search caches

The list algorithm creates duplicate-free label lists. Its established erasure
transports semantic cache validity and separation, giving bounds on the actual
computed cache rather than an assumed finite cache alphabet or size oracle.
-/
namespace ComplexCSP.ComplexityMaltsevCacheBounds
open MaltsevWitness MaltsevRelations
open PlanarHom PlanarHom.Complexity ComplexityEncodingBounds
variable {d n : ℕ} {A : Type} [DecidableEq A]

def CacheListsNodup (cache : ListTypeCache A) : Prop := ∀ e ∈ cache, e.2.Nodup

omit [DecidableEq A] in
private theorem cache_cons {len : ℕ} {xs : List A} {cache : ListTypeCache A}
    (hx : xs.Nodup) (hc : CacheListsNodup cache) : CacheListsNodup ((len,xs)::cache) := by
  intro e he
  rcases List.mem_cons.mp he with he | he
  · subst e
    exact hx
  · exact hc e he

private theorem fold_cache {children : List (Fin d)}
    (F : Fin d → ListTypeCache A → List A × ListTypeCache A)
    (hF : ∀ a c, CacheListsNodup c → CacheListsNodup (F a c).2)
    (state : List A × ListTypeCache A) (hc : CacheListsNodup state.2) :
    CacheListsNodup (children.foldl (fun state a =>
      let next := F a state.2; ((state.1 ++ next.1).dedup,next.2)) state).2 := by
  induction children generalizing state with
  | nil => exact hc
  | cons a children ih => exact ih _ (hF a _ hc)

/-- Every list newly stored by the runtime search is duplicate-free. -/
theorem materialized_cache_nodup (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (fuel len : ℕ) (target : Tuple (Fin d) n)
    (cache : ListTypeCache A) (hc : CacheListsNodup cache) :
    CacheListsNodup (materializedTypeSearch m W label fuel len target cache).2 := by
  induction fuel generalizing len target cache with
  | zero =>
    rw [materializedTypeSearch]
    cases hw : reconstructTo m W target len with
    | none => exact hc
    | some w =>
      simp only []
      cases ht : cachedTypeList cache len (label w) with
      | some S => exact hc
      | none => exact cache_cons (by simp) hc
  | succ fuel ih =>
    rw [materializedTypeSearch]
    cases hw : reconstructTo m W target len with
    | none => exact hc
    | some w =>
      simp only []
      cases ht : cachedTypeList cache len (label w) with
      | some S => exact hc
      | none =>
        by_cases hlt : len < n
        · simp only [dif_pos hlt]
          exact cache_cons (fold_type_nodup _ _ ([],cache) (by simp))
            (fold_cache _ (fun a c h => ih (len+1) _ c h) ([],cache) hc)
        · simpa only [dif_neg hlt] using cache_cons (len:=len) (by simp : [label w].Nodup) hc

/-- All semantic cache invariants are preserved from an arbitrary valid incoming
cache, including the intermediate caches of the depth-first computation. -/
theorem materialized_cache_invariants {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label)
    (fuel len : ℕ) (hdepth : len+fuel=n) (target : Tuple (Fin d) n)
    (cache : ListTypeCache A) (hv : CacheValid R label (eraseTypeCache cache))
    (hs : CacheSeparated (eraseTypeCache cache)) (hn : CacheListsNodup cache) :
    let output := (materializedTypeSearch m W label fuel len target cache).2
    CacheValid R label (eraseTypeCache output) ∧
      CacheSeparated (eraseTypeCache output) ∧ CacheListsNodup output := by
  have he : eraseTypeCache (materializedTypeSearch m W label fuel len target cache).2 =
      (typeSearch m W label fuel len target (eraseTypeCache cache)).2 :=
    congrArg Prod.snd (materializedTypeSearch_erase m W label fuel len target cache)
  refine ⟨?_,?_,materialized_cache_nodup m W label fuel len target cache hn⟩
  · rw [he]
    exact (typeSearch_correct hm hR hW label hTP fuel len hdepth target (eraseTypeCache cache) hv).2
  · rw [he]
    exact typeSearch_cache_separated hm hR hW label hTP fuel len hdepth target (eraseTypeCache cache) hv hs

/-- Semantic validity, separation and literal Nodup give finite cache bounds
without any numeric cache-size hypothesis. -/
theorem cache_bounds_of_invariants {R : Set (Fin n → Fin d)}
    {label : Tuple (Fin d) n → A} (cache : ListTypeCache A)
    (hv : CacheValid R label (eraseTypeCache cache))
    (hs : CacheSeparated (eraseTypeCache cache)) (hn : CacheListsNodup cache)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U) :
    cache.length ≤ (n+1)*U.card ∧
      ∀ e ∈ cache, e.1 ≤ n ∧ e.2.Nodup ∧ ∀ a ∈ e.2, a ∈ U := by
  constructor
  · simpa only [eraseTypeCache,List.length_map] using cache_length_le hv hs U hU
  · intro e he
    have hem : (e.1,e.2.toFinset) ∈ eraseTypeCache cache := List.mem_map.mpr ⟨e,he,rfl⟩
    obtain ⟨hl,_,x,hx⟩ := hv _ hem
    refine ⟨hl,hn e he,?_⟩
    intro a ha
    obtain ⟨y,hy,_,heq⟩ := (hx a).mp (List.mem_toFinset.mpr ha)
    exact heq ▸ hU y hy

/-- Actual returned cache entries have bounded levels, no repeated labels,
and labels realized on the relation. The number of entries is also proved. -/
theorem materialized_cache_bounds {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label)
    (fuel len : ℕ) (hdepth : len+fuel=n) (target : Tuple (Fin d) n)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U) :
    let cache := (materializedTypeSearch m W label fuel len target []).2
    cache.length ≤ (n+1)*U.card ∧
      ∀ e ∈ cache, e.1 ≤ n ∧ e.2.Nodup ∧ ∀ a ∈ e.2, a ∈ U := by
  let cache := (materializedTypeSearch m W label fuel len target []).2
  have he : eraseTypeCache cache = (typeSearch m W label fuel len target []).2 := by
    exact congrArg Prod.snd (materializedTypeSearch_erase m W label fuel len target [])
  have hv : CacheValid R label (eraseTypeCache cache) := by
    rw [he]
    exact (typeSearch_correct hm hR hW label hTP fuel len hdepth target [] (by
      intro e he; simp at he)).2
  have hn : CacheListsNodup cache := materialized_cache_nodup m W label fuel len target [] (by
    intro e he; simp at he)
  constructor
  · have hl := typeSearch_cache_length_le hm hR hW label hTP fuel len hdepth target U hU
    rw [← he] at hl
    simpa only [eraseTypeCache,List.length_map] using hl
  · intro e hec
    have hem : (e.1,e.2.toFinset) ∈ eraseTypeCache cache := List.mem_map.mpr ⟨e,hec,rfl⟩
    obtain ⟨hlevel,_,x,hx⟩ := hv _ hem
    refine ⟨hlevel,hn e hec,?_⟩
    intro a ha
    obtain ⟨y,hy,_,heq⟩ := (hx a).mp (List.mem_toFinset.mpr ha)
    exact heq ▸ hU y hy

/-- Bit-size bound for any cache satisfying the proved semantic invariants.
It charges binary levels and every framed label word. -/
theorem cache_code_bound (eA : BitEncoding A) (cache : ListTypeCache A) (U : Finset A)
    (B : ℕ) (hB : ∀ a ∈ U, (eA.encode a).length ≤ B)
    (hlen : cache.length ≤ (n+1)*U.card)
    (hentries : ∀ e ∈ cache, e.1 ≤ n ∧ e.2.Nodup ∧ ∀ a ∈ e.2, a ∈ U) :
    ((BitEncoding.nat.prod eA.list).list.encode cache).length ≤
      (6*(2*n+(6*B+3)*U.card+2)+3)*((n+1)*U.card)+1 := by
  have hentry : ∀ e ∈ cache, ((BitEncoding.nat.prod eA.list).encode e).length ≤
      2*n+(6*B+3)*U.card+2 := by
    intro e he
    obtain ⟨hl,hn,hmem⟩ := hentries e he
    have hs : e.2.toFinset ⊆ U := by intro a ha; exact hmem a (List.mem_toFinset.mp ha)
    have hcard : e.2.length ≤ U.card := by
      simpa only [List.toFinset_card_of_nodup hn] using Finset.card_le_card hs
    have hlist := encoded_list_le eA e.2 B (fun a ha => hB a (hmem a ha))
    have hi := (encodeNat_length_le e.1).trans hl
    rw [BitEncoding.prod_length]
    nlinarith
  have h := encoded_list_le (BitEncoding.nat.prod eA.list) cache
    (2*n+(6*B+3)*U.card+2) hentry
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hlen) 1)

end ComplexCSP.ComplexityMaltsevCacheBounds
