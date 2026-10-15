import ComplexCSP.Structure.MaltsevWitnessReindex
/-! Memoized prefix-type search, for finite common Mal'tsev witnesses.
The runtime classifier labels full support tuples; prefix feasibility is
computed using the proved witness reconstruction algorithm. -/
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ} {A : Type*} [DecidableEq A]
@[simp] theorem ofFn_view (x : Tuple (Fin d) n) : Vector.ofFn (view x) = x := view_injective (view_ofFn (view x))
def HasType (R : Set (Fin n → Fin d)) (label : Tuple (Fin d) n → A)
    (len : ℕ) (target : Tuple (Fin d) n) (a : A) : Prop :=
  ∃ x ∈ R, PrefixEq len x (view target) ∧ label (Vector.ofFn x) = a
def TypesPartition (R : Set (Fin n → Fin d)) (label : Tuple (Fin d) n → A) : Prop :=
  ∀ len, len ≤ n → ∀ x y : Tuple (Fin d) n,
    {a | HasType R label len x a} = {a | HasType R label len y a} ∨
      Disjoint {a | HasType R label len x a} {a | HasType R label len y a}
abbrev TypeCache (A : Type*) := List (ℕ × Finset A)
def DenotesType (R : Set (Fin n → Fin d)) (label : Tuple (Fin d) n → A)
    (len : ℕ) (target : Tuple (Fin d) n) (S : Finset (A)) : Prop :=
  ∀ a, a ∈ S ↔ HasType R label len target a
def CacheValid (R : Set (Fin n → Fin d)) (label : Tuple (Fin d) n → A) (cache : TypeCache A) : Prop :=
  ∀ entry ∈ cache, entry.1 ≤ n ∧ entry.2.Nonempty ∧ ∃ target, DenotesType R label entry.1 target entry.2
def cachedType (cache : TypeCache A) (len : ℕ) (a : A) : Option (Finset (A)) :=
  (cache.find? (fun e => decide (e.1 = len ∧ a ∈ e.2))).map Prod.snd
theorem cachedType_correct {R : Set (Fin n → Fin d)} {label : Tuple (Fin d) n → A}
    (hTP : TypesPartition R label) {cache : TypeCache A} (hcache : CacheValid R label cache)
    {len : ℕ} (hlen : len ≤ n) {target : Tuple (Fin d) n} {a : A} (ha : HasType R label len target a)
    {S : Finset (A)} (he : cachedType cache len a = some S) : DenotesType R label len target S := by
  obtain ⟨entry, hentry, rfl⟩ := Option.map_eq_some_iff.mp he
  have hemem := List.mem_of_find?_eq_some (show cache.find? _ = some entry from hentry)
  have hep := List.find?_some (show cache.find? _ = some entry from hentry)
  have hep' : entry.1 = len ∧ a ∈ entry.2 := of_decide_eq_true hep
  obtain ⟨_, _, z, hz⟩ := hcache entry hemem
  rw [hep'.1] at hz
  have hza := (hz a).mp hep'.2
  rcases hTP len hlen target z with heq | hdis
  · intro b
    exact (hz b).trans (Set.ext_iff.mp heq b).symm
  · exact False.elim (Set.disjoint_left.mp hdis ha hza)
omit [DecidableEq A] in
theorem hasType_of_reconstruct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (target : Tuple (Fin d) n) (len : ℕ) (hlen : len ≤ n)
    {w : Tuple (Fin d) n} (hw : reconstructTo m W target len = some w) : HasType R label len target (label w) := by
  exact ⟨view w, reconstructTo_sound hR hW _ _ hw, reconstructTo_prefix hm hW _ _ hlen hw, by simp⟩
omit [DecidableEq A] in
theorem full_type_singleton {R : Set (Fin n → Fin d)} {label : Tuple (Fin d) n → A}
    (target w : Tuple (Fin d) n) (hw : view w ∈ R) (hp : PrefixEq n (view w) (view target)) :
    DenotesType R label n target {label w} := by
  intro a
  simp only [Finset.mem_singleton]
  constructor
  · intro ha
    exact ⟨view w, hw, hp, by simpa using ha.symm⟩
  · rintro ⟨x, hx, hpx, hxa⟩
    have he : x = view w := (hpx.trans hp.symm).eq
    simpa [he] using hxa.symm
omit [DecidableEq A] in
theorem type_children (R : Set (Fin n → Fin d)) (label : Tuple (Fin d) n → A)
    (target : Tuple (Fin d) n) (i : Fin n) (b : A) :
    HasType R label i.val target b ↔ ∃ a : Fin d, HasType R label (i.val + 1) (replaceCoordinate target i a) b := by
  constructor
  · rintro ⟨x, hx, hp, hb⟩
    exact ⟨x i, x, hx, (prefix_replace_iff target i (x i) x).mpr ⟨hp.symm, rfl⟩, hb⟩
  · rintro ⟨a, x, hx, hp, hb⟩
    exact ⟨x, hx, ((prefix_replace_iff target i a x).mp hp).1.symm, hb⟩
def typeSearch (m : Operation (Fin d)) (W : Code (Fin d) n) (label : Tuple (Fin d) n → A) :
    ℕ → ℕ → Tuple (Fin d) n → TypeCache A → Finset (A) × TypeCache A
  | fuel, len, target, cache =>
    match reconstructTo m W target len with
    | none => (∅, cache)
    | some w =>
      match cachedType cache len (label w) with
      | some S => (S, cache)
      | none =>
        match fuel with
        | 0 => ({label w}, (len, {label w}) :: cache)
        | fuel + 1 =>
          if h : len < n then
            let result := (List.finRange d).foldl (fun state a =>
              let next := typeSearch m W label fuel (len + 1) (replaceCoordinate target ⟨len, h⟩ a) state.2
              (state.1 ∪ next.1, next.2)) (∅, cache)
            (result.1, (len, result.1) :: result.2)
          else ({label w}, (len, {label w}) :: cache)

omit [DecidableEq A] in
theorem cacheValid_cons {R : Set (Fin n → Fin d)} {label : Tuple (Fin d) n → A}
    {cache : TypeCache A} (hc : CacheValid R label cache) {len : ℕ} (hlen : len ≤ n)
    {target : Tuple (Fin d) n} {S : Finset (A)} (hS : S.Nonempty)
    (hden : DenotesType R label len target S) : CacheValid R label ((len, S) :: cache) := by
  intro e he
  rcases List.mem_cons.mp he with rfl | he
  · exact ⟨hlen, hS, target, hden⟩
  · exact hc e he

omit [DecidableEq A] in
theorem empty_type_of_reconstruct_none {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (target : Tuple (Fin d) n) (len : ℕ) (hlen : len ≤ n)
    (hw : reconstructTo m W target len = none) : DenotesType R label len target ∅ := by
  intro a
  constructor
  · simp
  · rintro ⟨x, hx, hp, _⟩
    have h := (reconstructTo_isSome_iff hm hR hW target len hlen).mpr ⟨x, hx, hp⟩
    simp [hw] at h

/-- A general checked left-fold invariant for the child searches. -/
theorem fold_types_spec (children : List (Fin d))
    (F : Fin d → TypeCache A → Finset (A) × TypeCache A)
    (P : Fin d → A → Prop) (Q : TypeCache A → Prop)
    (hF : ∀ a ∈ children, ∀ cache, Q cache →
      (∀ b, b ∈ (F a cache).1 ↔ P a b) ∧ Q (F a cache).2)
    (state : Finset (A) × TypeCache A) (hstate : Q state.2) :
    (∀ b, b ∈ (children.foldl (fun state a =>
      let next := F a state.2; (state.1 ∪ next.1, next.2)) state).1 ↔
        b ∈ state.1 ∨ ∃ a ∈ children, P a b) ∧
    Q (children.foldl (fun state a =>
      let next := F a state.2; (state.1 ∪ next.1, next.2)) state).2 := by
  induction children generalizing state with
  | nil => simpa using And.intro (fun b => Iff.rfl : ∀ b, b ∈ state.1 ↔ b ∈ state.1) hstate
  | cons a children ih =>
    obtain ⟨hhead, hQ⟩ := hF a List.mem_cons_self state.2 hstate
    have htail := ih (fun b hb => hF b (List.mem_cons_of_mem _ hb))
      (state.1 ∪ (F a state.2).1, (F a state.2).2) hQ
    refine ⟨?_, htail.2⟩
    intro b
    rw [List.foldl_cons]
    have h := htail.1 b
    simp only [Finset.mem_union, hhead, List.mem_cons] at h ⊢
    simpa only [Prod.fst, exists_eq_or_imp, or_assoc] using h

/-- Memoized prefix-type search computes exactly the semantic type, maintaining
only valid, nonempty cache entries. -/
theorem typeSearch_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n)
    (cache : TypeCache A) (hcache : CacheValid R label cache) :
    DenotesType R label len target (typeSearch m W label fuel len target cache).1 ∧
      CacheValid R label (typeSearch m W label fuel len target cache).2 := by
  have hlen : len ≤ n := by omega
  induction fuel generalizing len target cache with
  | zero =>
    have hln : len = n := by omega
    subst len
    rw [typeSearch]
    cases hw : reconstructTo m W target n with
    | none => exact ⟨empty_type_of_reconstruct_none hm hR hW label target n le_rfl hw, hcache⟩
    | some w =>
      simp only []
      cases hc : cachedType cache n (label w) with
      | some S =>
        exact ⟨cachedType_correct hTP hcache le_rfl (hasType_of_reconstruct hm hR hW label target n le_rfl hw) hc, hcache⟩
      | none =>
        have hden := full_type_singleton target w (reconstructTo_sound hR hW _ _ hw)
          (reconstructTo_prefix hm hW _ _ le_rfl hw) (label := label)
        exact ⟨hden, cacheValid_cons hcache le_rfl (Finset.singleton_nonempty _) hden⟩
  | succ fuel ih =>
    rw [typeSearch]
    cases hw : reconstructTo m W target len with
    | none => exact ⟨empty_type_of_reconstruct_none hm hR hW label target len hlen hw, hcache⟩
    | some w =>
      simp only []
      have hwtype := hasType_of_reconstruct hm hR hW label target len hlen hw
      cases hc : cachedType cache len (label w) with
      | some S => exact ⟨cachedType_correct hTP hcache hlen hwtype hc, hcache⟩
      | none =>
        have hlt : len < n := by omega
        simp only [dif_pos hlt]
        let F := fun a c => typeSearch m W label fuel (len + 1)
          (replaceCoordinate target ⟨len, hlt⟩ a) c
        have hF : ∀ a ∈ List.finRange d, ∀ c, CacheValid R label c →
            (∀ b, b ∈ (F a c).1 ↔ HasType R label (len + 1)
              (replaceCoordinate target ⟨len, hlt⟩ a) b) ∧ CacheValid R label (F a c).2 := by
          intro a _ c hc
          exact ih (len + 1) (by omega) _ c hc (by omega)
        have hfold := fold_types_spec (List.finRange d) F
          (fun a b => HasType R label (len + 1) (replaceCoordinate target ⟨len, hlt⟩ a) b)
          (CacheValid R label) hF (∅, cache) hcache
        let result := (List.finRange d).foldl (fun state a =>
          let next := F a state.2; (state.1 ∪ next.1, next.2)) (∅, cache)
        have hden : DenotesType R label len target result.1 := by
          intro b
          have hh := hfold.1 b
          simp only [Finset.notMem_empty, false_or, List.mem_finRange, true_and] at hh
          exact hh.trans (type_children R label target ⟨len, hlt⟩ b).symm
        have hnon : result.1.Nonempty := ⟨label w, (hden _).mpr hwtype⟩
        exact ⟨hden, cacheValid_cons hfold.2 hlen hnon hden⟩

end ComplexCSP.MaltsevWitness
