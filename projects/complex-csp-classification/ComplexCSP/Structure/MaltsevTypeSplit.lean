import ComplexCSP.Structure.MaltsevTypeCoordinates

/-! # Constructing each label-class witness function from Type Partition -/
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ} {A : Type*} [DecidableEq A]

def typeClassExtension (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) (a : Fin d)
    (z : Tuple (Fin d) n) : Option (Tuple (Fin d) n) :=
  labelExtension m W label wanted (n - (i.val + 1)) (i.val + 1) (replaceCoordinate z i a)

theorem typeClassExtension_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) (a : Fin d)
    (z : Tuple (Fin d) n) {result : Tuple (Fin d) n}
    (he : typeClassExtension m W label wanted i a z = some result) :
    view result ∈ labelFiber R label wanted ∧
      PrefixEq i.val (view z) (view result) ∧ view result i = a := by
  have hdepth : i.val + 1 + (n - (i.val + 1)) = n := by have := i.isLt; omega
  obtain ⟨hr, hp, hl⟩ := labelExtension_spec hm hR hW label wanted _ _ hdepth _ he
  exact ⟨⟨hr, by simpa using hl⟩, (prefix_replace_iff z i a _).mp hp⟩

theorem typeClassExtension_isSome {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label) (wanted : A)
    (i : Fin n) (a : Fin d) (z : Tuple (Fin d) n) :
    (typeClassExtension m W label wanted i a z).isSome = true ↔
      ∃ x ∈ labelFiber R label wanted, PrefixEq i.val (view z) x ∧ x i = a := by
  have hdepth : i.val + 1 + (n - (i.val + 1)) = n := by have := i.isLt; omega
  rw [typeClassExtension, labelExtension_isSome hm hR hW label hTP wanted _ _ hdepth]
  simp only [HasType, labelFiber, Set.mem_ofPred_eq, prefix_replace_iff]
  constructor
  · rintro ⟨x, hx, ⟨hp, hi⟩, hl⟩
    exact ⟨x, ⟨hx, hl⟩, hp, hi⟩
  · rintro ⟨x, ⟨hx, hl⟩, hp, hi⟩
    exact ⟨x, hx, ⟨hp, hi⟩, hl⟩

def typeClassCandidates (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) : List (Tuple (Fin d) n) :=
  (List.ofFn (typeCoordinateWitness m W label wanted i)).flatMap Option.toList

theorem typeClassCandidates_sound {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) {x : Tuple (Fin d) n}
    (hx : x ∈ typeClassCandidates m W label wanted i) : view x ∈ labelFiber R label wanted := by
  obtain ⟨v, hv, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hv
  exact (typeCoordinateWitness_spec hm hR hW label wanted i a (by simpa using hx)).1

theorem typeClassCandidates_complete {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : AllTypesPartition R label)
    (wanted : A) (i : Fin n) {x : Fin n → Fin d} (hx : x ∈ labelFiber R label wanted) :
    ∃ z ∈ typeClassCandidates m W label wanted i, view z i = x i := by
  obtain ⟨z, hz⟩ := typeCoordinateWitness_complete hm hR hW label hTP wanted i (x i) hx rfl
  refine ⟨z, ?_, (typeCoordinateWitness_spec hm hR hW label wanted i (x i) hz).2⟩
  exact List.mem_flatMap.mpr ⟨_, List.mem_ofFn.mpr ⟨x i, rfl⟩, by simpa using hz⟩

def typeClassAnchor (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) (a : Fin d) : Option (Tuple (Fin d) n) :=
  (typeClassCandidates m W label wanted i).find?
    (fun z => (typeClassExtension m W label wanted i a z).isSome)

def typeClassCode (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (wanted : A) (defaultValue : Fin d) : Code (Fin d) n where
  seed := labelExtension m W label wanted n 0 (Vector.ofFn (fun _ => defaultValue))
  lookup i a := (typeClassAnchor m W label wanted i a).bind
    (typeClassExtension m W label wanted i a)

theorem typeClassAnchor_congr {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label) (wanted : A)
    (hclass : Preserves m (labelFiber R label wanted)) {i : Fin n} {a b : Fin d}
    (hab : Fork (labelFiber R label wanted) i a b) :
    typeClassAnchor m W label wanted i a = typeClassAnchor m W label wanted i b := by
  apply congrArg (fun p => (typeClassCandidates m W label wanted i).find? p)
  funext z
  apply Bool.eq_iff_iff.mpr
  rw [typeClassExtension_isSome hm hR hW label hTP, typeClassExtension_isSome hm hR hW label hTP]
  constructor
  · rintro ⟨x, hx, hzx, hxa⟩
    obtain ⟨y, hy, hxy, hyb⟩ := fork_transport hm hclass hab hx hxa
    exact ⟨y, hy, hzx.trans hxy, hyb⟩
  · rintro ⟨x, hx, hzx, hxb⟩
    obtain ⟨y, hy, hxy, hya⟩ := fork_transport hm hclass (fork_symm hab) hx hxb
    exact ⟨y, hy, hzx.trans hxy, hya⟩

theorem typeClassCode_lookup_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (wanted : A) (defaultValue : Fin d)
    {i : Fin n} {a : Fin d} {result : Tuple (Fin d) n}
    (he : (typeClassCode m W label wanted defaultValue).lookup i a = some result) :
    ∃ z, typeClassAnchor m W label wanted i a = some z ∧
      view result ∈ labelFiber R label wanted ∧
      PrefixEq i.val (view z) (view result) ∧ view result i = a := by
  change (typeClassAnchor m W label wanted i a).bind _ = some result at he
  cases hz : typeClassAnchor m W label wanted i a with
  | none => simp [hz] at he
  | some z =>
    simp only [hz, Option.bind_some] at he
    exact ⟨z, rfl, typeClassExtension_spec hm hR hW label wanted i a z he⟩

/-- An actual witness function for each label class, including empty classes.
Only the literal Type Partition and common-polymorphism hypotheses are used. -/
theorem typeClassCode_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : AllTypesPartition R label)
    (wanted : A) (hclass : Preserves m (labelFiber R label wanted)) (defaultValue : Fin d) :
    Correct (typeClassCode m W label wanted defaultValue) (labelFiber R label wanted) := by
  constructor
  · intro x hx
    have hs := labelExtension_spec hm hR hW label wanted n 0 (by omega) _ hx
    exact ⟨hs.1, by simpa using hs.2.2⟩
  · rintro ⟨x, hx, hl⟩
    apply labelExtension_complete hm hR hW label hTP.base wanted n 0 (by omega)
    exact ⟨x, hx, by intro i hi; omega, hl⟩
  · intro i a x hx
    obtain ⟨_, _, hxR, _, hxa⟩ := typeClassCode_lookup_spec hm hR hW label wanted defaultValue hx
    exact ⟨hxR, hxa⟩
  · intro i x hx
    obtain ⟨z, hz, hzi⟩ := typeClassCandidates_complete hm hR hW label hTP wanted i hx
    have hzR := typeClassCandidates_sound hm hR hW label wanted i hz
    have he : (typeClassExtension m W label wanted i (x i) z).isSome = true :=
      (typeClassExtension_isSome hm hR hW label hTP.base wanted i (x i) z).mpr
        ⟨view z, hzR, PrefixEq.refl _ _, hzi⟩
    have ha : (typeClassAnchor m W label wanted i (x i)).isSome = true :=
      List.find?_isSome.mpr ⟨z, hz, he⟩
    cases hu : typeClassAnchor m W label wanted i (x i) with
    | none => simp [hu] at ha
    | some u =>
      have ht := List.find?_some
        (show (typeClassCandidates m W label wanted i).find? _ = some u from hu)
      cases hr : typeClassExtension m W label wanted i (x i) u with
      | none => simp [hr] at ht
      | some result => exact ⟨result, by simp [typeClassCode, hu, hr]⟩
  · intro i a b x y hab hx hy
    obtain ⟨u, hu, _, hux, _⟩ := typeClassCode_lookup_spec hm hR hW label wanted defaultValue hx
    obtain ⟨v, hv, _, hvy, _⟩ := typeClassCode_lookup_spec hm hR hW label wanted defaultValue hy
    have huv : u = v := Option.some.inj
      (hu.symm.trans ((typeClassAnchor_congr hm hR hW label hTP.base wanted hclass hab).trans hv))
    subst v
    exact hux.symm.trans hvy


/-- Enumerate actual labels and materialize their computed witness tables. -/
def splitTypeClasses (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (defaultValue : Fin d) : List (A × StoredCode d n) :=
  (materializedTypeSearch m W label n 0 (Vector.ofFn (fun _ => defaultValue)) []).1.map
    (fun a => (a, storeCode (typeClassCode m W label a defaultValue)))

theorem splitTypeClasses_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : AllTypesPartition R label)
    (hclasses : ∀ a, Preserves m (labelFiber R label a)) (defaultValue : Fin d) :
    ∀ entry ∈ splitTypeClasses m W label defaultValue,
      Correct entry.2.toCode (labelFiber R label entry.1) := by
  intro entry he
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp he
  simpa only [storeCode_toCode] using typeClassCode_correct hm hR hW label hTP a (hclasses a) defaultValue

theorem splitTypeClasses_labels {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : AllTypesPartition R label)
    (defaultValue : Fin d) (a : A) :
    a ∈ (splitTypeClasses m W label defaultValue).map Prod.fst ↔
      ∃ x ∈ R, label (Vector.ofFn x) = a := by
  have h := materializedTypeSearch_correct hm hR hW label hTP.base n 0 (by omega)
    (Vector.ofFn (fun _ => defaultValue)) a
  simpa [splitTypeClasses, List.map_map, HasType, PrefixEq] using h

theorem splitTypeClasses_nodup (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (defaultValue : Fin d) :
    ((splitTypeClasses m W label defaultValue).map Prod.fst).Nodup := by
  simpa [splitTypeClasses, List.map_map, Function.comp_def] using materializedTypeSearch_nodup m W label n 0
    (Vector.ofFn (fun _ => defaultValue)) []

/-- The actual returned class list has no more entries than the actual label
image; in the weighted application literal BO supplies an image bound of d. -/
theorem splitTypeClasses_length_le {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : AllTypesPartition R label) (defaultValue : Fin d)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U) :
    (splitTypeClasses m W label defaultValue).length ≤ U.card := by
  simpa only [splitTypeClasses, List.length_map] using materializedTypeSearch_length_le
    hm hR hW label hTP.base n 0 (by omega) (Vector.ofFn (fun _ => defaultValue)) U hU

end ComplexCSP.MaltsevWitness
