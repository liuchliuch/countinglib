import ComplexCSP.Structure.MaltsevTypeSearch

/-! # Cache invariants for the memoized type algorithm -/
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ} {A : Type*} [DecidableEq A]

def CacheOrigin (lower : ℕ) (before after : TypeCache A) : Prop :=
  ∀ e ∈ after, e ∈ before ∨ lower ≤ e.1

def CacheSeparated (cache : TypeCache A) : Prop :=
  cache.Pairwise (fun x y => x.1 ≠ y.1 ∨ Disjoint x.2 y.2)

theorem fold_cache_origin (children : List (Fin d))
    (F : Fin d → TypeCache A → Finset A × TypeCache A) (lower : ℕ)
    (hF : ∀ a c, CacheOrigin lower c (F a c).2) (state : Finset A × TypeCache A) :
    CacheOrigin lower state.2 (children.foldl (fun state a =>
      let next := F a state.2; (state.1 ∪ next.1, next.2)) state).2 := by
  induction children generalizing state with
  | nil => exact fun _ h => Or.inl h
  | cons a children ih =>
    intro e he
    rcases ih (state.1 ∪ (F a state.2).1, (F a state.2).2) e he with h | h
    · exact hF a state.2 e h
    · exact Or.inr h

theorem typeSearch_cache_origin (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (fuel len : ℕ) (target : Tuple (Fin d) n) (cache : TypeCache A) :
    CacheOrigin len cache (typeSearch m W label fuel len target cache).2 := by
  induction fuel generalizing len target cache with
  | zero =>
    rw [typeSearch]
    cases hw : reconstructTo m W target len with
    | none => exact fun _ h => Or.inl h
    | some w =>
      simp only []
      cases hc : cachedType cache len (label w) with
      | some S => exact fun _ h => Or.inl h
      | none =>
        intro e he
        rcases List.mem_cons.mp he with rfl | he
        · exact Or.inr le_rfl
        · exact Or.inl he
  | succ fuel ih =>
    rw [typeSearch]
    cases hw : reconstructTo m W target len with
    | none => exact fun _ h => Or.inl h
    | some w =>
      simp only []
      cases hc : cachedType cache len (label w) with
      | some S => exact fun _ h => Or.inl h
      | none =>
        by_cases hlt : len < n
        · simp only [dif_pos hlt]
          let F := fun a c => typeSearch m W label fuel (len + 1)
            (replaceCoordinate target ⟨len, hlt⟩ a) c
          have hF : ∀ a c, CacheOrigin len c (F a c).2 := by
            intro a c e he
            rcases ih (len + 1) _ c e he with h | h
            · exact Or.inl h
            · exact Or.inr (by omega)
          have hf := fold_cache_origin (List.finRange d) F len hF (∅, cache)
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact Or.inr le_rfl
          · exact hf e he
        · simp only [dif_neg hlt]
          intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact Or.inr le_rfl
          · exact Or.inl he

theorem cachedType_none {cache : TypeCache A} {len : ℕ} {a : A}
    (h : cachedType cache len a = none) : ∀ e ∈ cache, e.1 = len → a ∉ e.2 := by
  have hn : cache.find? (fun e => decide (e.1 = len ∧ a ∈ e.2)) = none := by
    simpa [cachedType] using h
  intro e he hlen ha
  have hf := List.find?_eq_none.mp hn e he
  exact hf (by simp [hlen, ha])

omit [DecidableEq A] in
theorem separated_type_cons {R : Set (Fin n → Fin d)} {label : Tuple (Fin d) n → A}
    (hTP : TypesPartition R label) {cache : TypeCache A} (hv : CacheValid R label cache)
    (hs : CacheSeparated cache) {len : ℕ} (hlen : len ≤ n) {target : Tuple (Fin d) n}
    {S : Finset A} (hden : DenotesType R label len target S) {a : A} (ha : a ∈ S)
    (hmiss : ∀ e ∈ cache, e.1 = len → a ∉ e.2) : CacheSeparated ((len, S) :: cache) := by
  apply List.pairwise_cons.mpr
  refine ⟨?_, hs⟩
  intro e he
  by_cases hl : len = e.1
  · right
    obtain ⟨_, _, z, hz⟩ := hv e he
    rw [← hl] at hz
    rcases hTP len hlen target z with heq | hdis
    · have hzmem : a ∈ e.2 := (hz a).mpr ((Set.ext_iff.mp heq a).mp ((hden a).mp ha))
      exact False.elim (hmiss e he hl.symm hzmem)
    · apply Finset.disjoint_left.mpr
      intro b hb hb'
      exact Set.disjoint_left.mp hdis ((hden b).mp hb) ((hz b).mp hb')
  · exact Or.inl hl

/-- Computed cache types at the same depth are pairwise disjoint. -/
theorem typeSearch_cache_separated {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n)
    (cache : TypeCache A) (hv : CacheValid R label cache) (hs : CacheSeparated cache) :
    CacheSeparated (typeSearch m W label fuel len target cache).2 := by
  induction fuel generalizing len target cache with
  | zero =>
    have hln : len = n := by omega
    subst len
    rw [typeSearch]
    cases hw : reconstructTo m W target n with
    | none => exact hs
    | some w =>
      simp only []
      cases hc : cachedType cache n (label w) with
      | some S => exact hs
      | none =>
        have hd := full_type_singleton target w (reconstructTo_sound hR hW _ _ hw)
          (reconstructTo_prefix hm hW _ _ le_rfl hw) (label := label)
        exact separated_type_cons hTP hv hs le_rfl hd (Finset.mem_singleton_self _) (cachedType_none hc)
  | succ fuel ih =>
    have hlen : len ≤ n := by omega
    rw [typeSearch]
    cases hw : reconstructTo m W target len with
    | none => exact hs
    | some w =>
      simp only []
      cases hc : cachedType cache len (label w) with
      | some S => exact hs
      | none =>
        have hlt : len < n := by omega
        simp only [dif_pos hlt]
        let F := fun a c => typeSearch m W label fuel (len + 1)
          (replaceCoordinate target ⟨len, hlt⟩ a) c
        have hF : ∀ a ∈ List.finRange d, ∀ c, CacheValid R label c ∧ CacheSeparated c →
            (∀ b, b ∈ (F a c).1 ↔ HasType R label (len + 1)
              (replaceCoordinate target ⟨len, hlt⟩ a) b) ∧
            CacheValid R label (F a c).2 ∧ CacheSeparated (F a c).2 := by
          intro a _ c hc
          have ht := typeSearch_correct hm hR hW label hTP fuel (len + 1) (by omega)
            (replaceCoordinate target ⟨len, hlt⟩ a) c hc.1
          exact ⟨ht.1, ht.2, ih (len + 1) (by omega) _ c hc.1 hc.2⟩
        have hfold := fold_types_spec (List.finRange d) F
          (fun a b => HasType R label (len + 1) (replaceCoordinate target ⟨len, hlt⟩ a) b)
          (fun c => CacheValid R label c ∧ CacheSeparated c) hF (∅, cache) ⟨hv, hs⟩
        let result := (List.finRange d).foldl (fun state a =>
          let next := F a state.2; (state.1 ∪ next.1, next.2)) (∅, cache)
        have hden : DenotesType R label len target result.1 := by
          intro b
          have hh := hfold.1 b
          simp only [Finset.notMem_empty, false_or, List.mem_finRange, true_and] at hh
          exact hh.trans (type_children R label target ⟨len, hlt⟩ b).symm
        have horigin : CacheOrigin (len + 1) cache result.2 :=
          fold_cache_origin (List.finRange d) F (len + 1)
            (fun a c => typeSearch_cache_origin m W label fuel (len + 1) _ c) (∅, cache)
        have hmem : label w ∈ result.1 :=
          (hden _).mpr (hasType_of_reconstruct hm hR hW label target len hlen hw)
        apply separated_type_cons hTP hfold.2.1 hfold.2.2 hlen hden hmem
        intro e he hel
        rcases horigin e he with he | he
        · exact cachedType_none hc e he hel
        · omega


omit [DecidableEq A] in
/-- There are at most `(n+1)*|U|` cached types when all actual labels belong to
`U`. This is a mathematical bound on the literal computed cache list. -/
theorem cache_length_le {R : Set (Fin n → Fin d)} {label : Tuple (Fin d) n → A}
    {cache : TypeCache A} (hv : CacheValid R label cache) (hs : CacheSeparated cache)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U) :
    cache.length ≤ (n + 1) * U.card := by
  classical
  have hentry : ∀ i : Fin cache.length, ∃ a, a ∈ (cache.get i).2 ∧ a ∈ U := by
    intro i
    obtain ⟨_, hne, z, hz⟩ := hv (cache.get i) (List.get_mem _ _)
    obtain ⟨a, ha⟩ := hne
    obtain ⟨x, hx, _, hlabel⟩ := (hz a).mp ha
    exact ⟨a, ha, hlabel ▸ hU x hx⟩
  choose pick hpick hpinU using hentry
  let encode : Fin cache.length → Fin (n + 1) × U := fun i =>
    (⟨(cache.get i).1, Nat.lt_succ_of_le (hv _ (List.get_mem _ _)).1⟩,
      ⟨pick i, hpinU i⟩)
  have hne : ∀ i j : Fin cache.length, i < j → encode i ≠ encode j := by
    intro i j hij he
    have hlevel : (cache.get i).1 = (cache.get j).1 :=
      congrArg (fun p : Fin (n + 1) × U => p.1.val) he
    have hlabel : pick i = pick j := congrArg (fun p : Fin (n + 1) × U => p.2.val) he
    rcases List.pairwise_iff_get.mp hs i j hij with hbad | hdis
    · exact hbad hlevel
    · exact Finset.disjoint_left.mp hdis (hpick i) (hlabel.symm ▸ hpick j)
  have hinj : Function.Injective encode := by
    intro i j he
    rcases lt_trichotomy i j with h | h | h
    · exact False.elim (hne i j h he)
    · exact h
    · exact False.elim (hne j i h he.symm)
  simpa using Fintype.card_le_of_injective encode hinj

/-- Uniform linear bound on the computed cache for a bounded actual label image. -/
theorem typeSearch_cache_length_le {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U) :
    (typeSearch m W label fuel len target []).2.length ≤ (n + 1) * U.card := by
  have hv : CacheValid R label ([] : TypeCache A) := by intro e he; simp at he
  have hs : CacheSeparated ([] : TypeCache A) := by simp [CacheSeparated]
  exact cache_length_le
    (typeSearch_correct hm hR hW label hTP fuel len hdepth target [] hv).2
    (typeSearch_cache_separated hm hR hW label hTP fuel len hdepth target [] hv hs) U hU

end ComplexCSP.MaltsevWitness
