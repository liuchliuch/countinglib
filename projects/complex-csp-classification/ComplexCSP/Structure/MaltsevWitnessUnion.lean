import ComplexCSP.Structure.MaltsevWitnessConstruction
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {ι : Type*} {d n : ℕ}
def familyUnion (indices : List ι) (R : ι → Set (Fin n → Fin d)) : Set (Fin n → Fin d) :=
  {x | ∃ p ∈ indices, x ∈ R p}
def replaceCoordinate (z : Tuple (Fin d) n) (i : Fin n) (a : Fin d) : Tuple (Fin d) n :=
  Vector.ofFn (Function.update (view z) i a)
theorem prefix_replace_iff (z : Tuple (Fin d) n) (i : Fin n) (a : Fin d) (x : Fin n → Fin d) :
    PrefixEq (i.val + 1) x (view (replaceCoordinate z i a)) ↔
      PrefixEq i.val (view z) x ∧ x i = a := by
  simp only [replaceCoordinate, view_ofFn]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro j hj
      have hji : j ≠ i := by intro he; subst j; omega
      simpa [Function.update_of_ne hji] using (h j (by omega)).symm
    · simpa using h i (by omega)
  · rintro ⟨hp, hi⟩ j hj
    by_cases hji : j = i
    · subst j; simpa using hi
    · have hj' : j.val < i.val := by
        have : j.val ≠ i.val := fun he => hji (Fin.ext he)
        omega
      simpa [Function.update_of_ne hji] using (hp j hj').symm
def unionExtension (m : Operation (Fin d)) (indices : List ι) (W : ι → Code (Fin d) n)
    (i : Fin n) (a : Fin d) (z : Tuple (Fin d) n) : Option (Tuple (Fin d) n) :=
  indices.findSome? (fun p => reconstructTo m (W p) (replaceCoordinate z i a) (i.val + 1))
theorem unionExtension_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {indices : List ι} {W : ι → Code (Fin d) n} {R : ι → Set (Fin n → Fin d)}
    (hW : ∀ p ∈ indices, Correct (W p) (R p)) (hR : ∀ p ∈ indices, Preserves m (R p))
    {i : Fin n} {a : Fin d} {z result : Tuple (Fin d) n}
    (h : unionExtension m indices W i a z = some result) :
    view result ∈ familyUnion indices R ∧ PrefixEq i.val (view z) (view result) ∧ view result i = a := by
  obtain ⟨p, hp, he⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨⟨p, hp, reconstructTo_sound (hR p hp) (hW p hp) _ _ he⟩, ?_⟩
  exact (prefix_replace_iff z i a _).mp (reconstructTo_prefix hm (hW p hp) _ _ (by omega) he)
theorem unionExtension_isSome {m : Operation (Fin d)} (hm : IsMaltsev m)
    {indices : List ι} {W : ι → Code (Fin d) n} {R : ι → Set (Fin n → Fin d)}
    (hW : ∀ p ∈ indices, Correct (W p) (R p)) (hR : ∀ p ∈ indices, Preserves m (R p))
    (i : Fin n) (a : Fin d) (z : Tuple (Fin d) n) :
    (unionExtension m indices W i a z).isSome = true ↔
      ∃ x ∈ familyUnion indices R, PrefixEq i.val (view z) x ∧ x i = a := by
  simp only [unionExtension, List.findSome?_isSome_iff]
  constructor
  · rintro ⟨p, hp, he⟩
    obtain ⟨x, hx, hpx⟩ := (reconstructTo_isSome_iff hm (hR p hp) (hW p hp) _ _ (by omega)).mp he
    exact ⟨x, ⟨p, hp, hx⟩, (prefix_replace_iff z i a _).mp hpx⟩
  · rintro ⟨x, ⟨p, hp, hx⟩, hpx⟩
    exact ⟨p, hp, (reconstructTo_isSome_iff hm (hR p hp) (hW p hp) _ _ (by omega)).mpr
      ⟨x, hx, (prefix_replace_iff z i a _).mpr hpx⟩⟩
def unionCandidates (indices : List ι) (W : ι → Code (Fin d) n) (i : Fin n) : List (Tuple (Fin d) n) :=
  indices.flatMap (fun p => (List.ofFn ((W p).lookup i)).flatMap Option.toList)
theorem mem_unionCandidates_iff (indices : List ι) (W : ι → Code (Fin d) n) (i : Fin n) (x : Tuple (Fin d) n) :
    x ∈ unionCandidates indices W i ↔ ∃ p ∈ indices, ∃ a, (W p).lookup i a = some x := by
  simp [unionCandidates, List.mem_flatMap, List.mem_ofFn, Option.mem_toList]
def unionAnchor (m : Operation (Fin d)) (indices : List ι) (W : ι → Code (Fin d) n)
    (i : Fin n) (a : Fin d) : Option (Tuple (Fin d) n) :=
  (unionCandidates indices W i).find? (fun z => (unionExtension m indices W i a z).isSome)
def unionCode (m : Operation (Fin d)) (indices : List ι) (W : ι → Code (Fin d) n) : Code (Fin d) n where
  seed := indices.findSome? (fun p => (W p).seed)
  lookup i a := (unionAnchor m indices W i a).bind (unionExtension m indices W i a)
theorem unionAnchor_congr {m : Operation (Fin d)} (hm : IsMaltsev m)
    {indices : List ι} {W : ι → Code (Fin d) n} {R : ι → Set (Fin n → Fin d)}
    (hW : ∀ p ∈ indices, Correct (W p) (R p)) (hR : ∀ p ∈ indices, Preserves m (R p))
    (hU : Preserves m (familyUnion indices R)) {i : Fin n} {a b : Fin d}
    (hab : Fork (familyUnion indices R) i a b) : unionAnchor m indices W i a = unionAnchor m indices W i b := by
  have he : ∀ z : Tuple (Fin d) n,
      (unionExtension m indices W i a z).isSome = (unionExtension m indices W i b z).isSome := by
    intro z
    apply Bool.eq_iff_iff.mpr
    rw [unionExtension_isSome hm hW hR, unionExtension_isSome hm hW hR]
    constructor
    · rintro ⟨x, hx, hzx, hxa⟩
      obtain ⟨y, hy, hxy, hyb⟩ := fork_transport hm hU hab hx hxa
      exact ⟨y, hy, hzx.trans hxy, hyb⟩
    · rintro ⟨x, hx, hzx, hxb⟩
      obtain ⟨y, hy, hxy, hya⟩ := fork_transport hm hU (fork_symm hab) hx hxb
      exact ⟨y, hy, hzx.trans hxy, hya⟩
  exact congrArg (fun p => (unionCandidates indices W i).find? p) (funext he)
theorem unionCode_lookup_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {indices : List ι} {W : ι → Code (Fin d) n} {R : ι → Set (Fin n → Fin d)}
    (hW : ∀ p ∈ indices, Correct (W p) (R p)) (hR : ∀ p ∈ indices, Preserves m (R p))
    {i : Fin n} {a : Fin d} {result : Tuple (Fin d) n}
    (h : (unionCode m indices W).lookup i a = some result) :
    ∃ z, unionAnchor m indices W i a = some z ∧ view result ∈ familyUnion indices R ∧
      PrefixEq i.val (view z) (view result) ∧ view result i = a := by
  change (unionAnchor m indices W i a).bind (unionExtension m indices W i a) = some result at h
  cases he : unionAnchor m indices W i a with
  | none => simp [he] at h
  | some z =>
    simp only [he, Option.bind_some] at h
    exact ⟨z, rfl, unionExtension_spec hm hW hR h⟩
theorem unionCode_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {indices : List ι} {W : ι → Code (Fin d) n} {R : ι → Set (Fin n → Fin d)}
    (hW : ∀ p ∈ indices, Correct (W p) (R p)) (hR : ∀ p ∈ indices, Preserves m (R p))
    (hU : Preserves m (familyUnion indices R)) : Correct (unionCode m indices W) (familyUnion indices R) := by
  constructor
  · intro x hx
    obtain ⟨p, hp, he⟩ := List.exists_of_findSome?_eq_some hx
    exact ⟨p, hp, (hW p hp).seed_sound _ he⟩
  · rintro ⟨x, p, hp, hx⟩
    obtain ⟨z, hz⟩ := (hW p hp).seed_complete ⟨x, hx⟩
    have hs : (indices.findSome? (fun p => (W p).seed)).isSome = true :=
      List.findSome?_isSome_iff.mpr ⟨p, hp, by simp [hz]⟩
    cases hh : indices.findSome? (fun p => (W p).seed) with
    | none => simp [hh] at hs
    | some y => exact ⟨y, hh⟩
  · intro i a x hx
    obtain ⟨_, _, hxR, _, hxa⟩ := unionCode_lookup_spec hm hW hR hx
    exact ⟨hxR, hxa⟩
  · rintro i x ⟨p, hp, hx⟩
    obtain ⟨y, hy⟩ := (hW p hp).lookup_complete i x hx
    obtain ⟨hyR, hyi⟩ := (hW p hp).lookup_sound _ _ _ hy
    have hc : y ∈ unionCandidates indices W i :=
      (mem_unionCandidates_iff _ _ _ _).mpr ⟨p, hp, x i, hy⟩
    have he : (unionExtension m indices W i (x i) y).isSome = true :=
      (unionExtension_isSome hm hW hR _ _ _).mpr ⟨view y, ⟨p, hp, hyR⟩, PrefixEq.refl _ _, hyi⟩
    have ha : (unionAnchor m indices W i (x i)).isSome = true := List.find?_isSome.mpr ⟨y, hc, he⟩
    cases hh : unionAnchor m indices W i (x i) with
    | none => simp [hh] at ha
    | some anchor =>
      have hn := List.find?_some (show (unionCandidates indices W i).find? _ = some anchor from hh)
      cases hz : unionExtension m indices W i (x i) anchor with
      | none => simp [hz] at hn
      | some result => exact ⟨result, by simp [unionCode, hh, hz]⟩
  · intro i a b x y hab hx hy
    obtain ⟨u, hu, _, hux, _⟩ := unionCode_lookup_spec hm hW hR hx
    obtain ⟨v, hv, _, hvy, _⟩ := unionCode_lookup_spec hm hW hR hy
    have huv : u = v := Option.some.inj (hu.symm.trans ((unionAnchor_congr hm hW hR hU hab).trans hv))
    subst v
    exact hux.symm.trans hvy
end ComplexCSP.MaltsevWitness
