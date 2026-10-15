import ComplexCSP.Structure.MaltsevTypeRestriction
import ComplexCSP.Structure.MaltsevTypeSplit

/-! # Actual class witnesses by unary coordinate pinning

This alternate constructor uses the unchanged original row callback. It is
proved Correct in its own right; no identity with the old permuted witness
choices is asserted or needed.
-/
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ} {A : Type*} [DecidableEq A]

def pinnedTypeCoordinateWitness (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) (a : Fin d) : Option (Tuple (Fin d) n) :=
  labelExtension m (coordinatePinCode m W i a).toCode label wanted n 0 (Vector.ofFn (fun _ => a))

theorem pinnedTypeCoordinateWitness_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) (a : Fin d) {result : Tuple (Fin d) n}
    (he : pinnedTypeCoordinateWitness m W label wanted i a = some result) :
    view result ∈ labelFiber R label wanted ∧ view result i = a := by
  have hP := coordinatePinCode_correct hm hR hW i a
  obtain ⟨hr,hprefix,hl⟩ := labelExtension_spec hm (coordinatePin_preserves hm hR i a) hP
    label wanted n 0 (by omega) _ he
  exact ⟨⟨hr.1,by simpa only [ofFn_view] using hl⟩,hr.2⟩

theorem pinnedTypeCoordinateWitness_complete {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hEq : PreservesRowEquivalence m (labelFiber R label))
    (wanted : A) (i : Fin n) (a : Fin d) {x : Fin n → Fin d}
    (hx : x ∈ labelFiber R label wanted) (hxi : x i = a) :
    ∃ result, pinnedTypeCoordinateWitness m W label wanted i a = some result := by
  have hP := coordinatePinCode_correct hm hR hW i a
  apply labelExtension_complete hm (coordinatePin_preserves hm hR i a) hP label
    (coordinatePin_typesPartition hm hEq i a) wanted n 0 (by omega)
  exact ⟨x,⟨hx.1,hxi⟩,by intro j hj; omega,hx.2⟩

def pinnedTypeClassCandidates (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) : List (Tuple (Fin d) n) :=
  (List.ofFn (pinnedTypeCoordinateWitness m W label wanted i)).flatMap Option.toList

theorem pinnedTypeClassCandidates_sound {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) {x : Tuple (Fin d) n}
    (hx : x ∈ pinnedTypeClassCandidates m W label wanted i) : view x ∈ labelFiber R label wanted := by
  obtain ⟨v, hv, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨a, rfl⟩ := List.mem_ofFn.mp hv
  exact (pinnedTypeCoordinateWitness_spec hm hR hW label wanted i a (by simpa using hx)).1

theorem pinnedTypeClassCandidates_complete {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hEq : PreservesRowEquivalence m (labelFiber R label))
    (wanted : A) (i : Fin n) {x : Fin n → Fin d} (hx : x ∈ labelFiber R label wanted) :
    ∃ z ∈ pinnedTypeClassCandidates m W label wanted i, view z i = x i := by
  obtain ⟨z, hz⟩ := pinnedTypeCoordinateWitness_complete hm hR hW label hEq wanted i (x i) hx rfl
  refine ⟨z, ?_, (pinnedTypeCoordinateWitness_spec hm hR hW label wanted i (x i) hz).2⟩
  exact List.mem_flatMap.mpr ⟨_, List.mem_ofFn.mpr ⟨x i, rfl⟩, by simpa using hz⟩

def pinnedTypeClassAnchor (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) (a : Fin d) : Option (Tuple (Fin d) n) :=
  (pinnedTypeClassCandidates m W label wanted i).find?
    (fun z => (typeClassExtension m W label wanted i a z).isSome)

def pinnedTypeClassCode (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (wanted : A) (defaultValue : Fin d) : Code (Fin d) n where
  seed := labelExtension m W label wanted n 0 (Vector.ofFn (fun _ => defaultValue))
  lookup i a := (pinnedTypeClassAnchor m W label wanted i a).bind
    (typeClassExtension m W label wanted i a)

theorem pinnedTypeClassAnchor_congr {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label) (wanted : A)
    (hclass : Preserves m (labelFiber R label wanted)) {i : Fin n} {a b : Fin d}
    (hab : Fork (labelFiber R label wanted) i a b) :
    pinnedTypeClassAnchor m W label wanted i a = pinnedTypeClassAnchor m W label wanted i b := by
  apply congrArg (fun p => (pinnedTypeClassCandidates m W label wanted i).find? p)
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

theorem pinnedTypeClassCode_lookup_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (wanted : A) (defaultValue : Fin d)
    {i : Fin n} {a : Fin d} {result : Tuple (Fin d) n}
    (he : (pinnedTypeClassCode m W label wanted defaultValue).lookup i a = some result) :
    ∃ z, pinnedTypeClassAnchor m W label wanted i a = some z ∧
      view result ∈ labelFiber R label wanted ∧
      PrefixEq i.val (view z) (view result) ∧ view result i = a := by
  change (pinnedTypeClassAnchor m W label wanted i a).bind _ = some result at he
  cases hz : pinnedTypeClassAnchor m W label wanted i a with
  | none => simp [hz] at he
  | some z =>
    simp only [hz, Option.bind_some] at he
    exact ⟨z, rfl, typeClassExtension_spec hm hR hW label wanted i a z he⟩

/-- An actual witness function for each label class, including empty classes.
Only the literal Type Partition and common-polymorphism hypotheses are used. -/
theorem pinnedTypeClassCode_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hEq : PreservesRowEquivalence m (labelFiber R label))
    (wanted : A) (defaultValue : Fin d) :
    Correct (pinnedTypeClassCode m W label wanted defaultValue) (labelFiber R label wanted) := by
  have hTP := allTypesPartition_of_row_equivalence hm hEq
  have hclass := row_equivalence_fibers_preserves hm hEq wanted
  constructor
  · intro x hx
    have hs := labelExtension_spec hm hR hW label wanted n 0 (by omega) _ hx
    exact ⟨hs.1, by simpa using hs.2.2⟩
  · rintro ⟨x, hx, hl⟩
    apply labelExtension_complete hm hR hW label hTP.base wanted n 0 (by omega)
    exact ⟨x, hx, by intro i hi; omega, hl⟩
  · intro i a x hx
    obtain ⟨_, _, hxR, _, hxa⟩ := pinnedTypeClassCode_lookup_spec hm hR hW label wanted defaultValue hx
    exact ⟨hxR, hxa⟩
  · intro i x hx
    obtain ⟨z, hz, hzi⟩ := pinnedTypeClassCandidates_complete hm hR hW label hEq wanted i hx
    have hzR := pinnedTypeClassCandidates_sound hm hR hW label wanted i hz
    have he : (typeClassExtension m W label wanted i (x i) z).isSome = true :=
      (typeClassExtension_isSome hm hR hW label hTP.base wanted i (x i) z).mpr
        ⟨view z, hzR, PrefixEq.refl _ _, hzi⟩
    have ha : (pinnedTypeClassAnchor m W label wanted i (x i)).isSome = true :=
      List.find?_isSome.mpr ⟨z, hz, he⟩
    cases hu : pinnedTypeClassAnchor m W label wanted i (x i) with
    | none => simp [hu] at ha
    | some u =>
      have ht := List.find?_some
        (show (pinnedTypeClassCandidates m W label wanted i).find? _ = some u from hu)
      cases hr : typeClassExtension m W label wanted i (x i) u with
      | none => simp [hr] at ht
      | some result => exact ⟨result, by simp [pinnedTypeClassCode, hu, hr]⟩
  · intro i a b x y hab hx hy
    obtain ⟨u, hu, _, hux, _⟩ := pinnedTypeClassCode_lookup_spec hm hR hW label wanted defaultValue hx
    obtain ⟨v, hv, _, hvy, _⟩ := pinnedTypeClassCode_lookup_spec hm hR hW label wanted defaultValue hy
    have huv : u = v := Option.some.inj
      (hu.symm.trans ((pinnedTypeClassAnchor_congr hm hR hW label hTP.base wanted hclass hab).trans hv))
    subst v
    exact hux.symm.trans hvy


/-- Enumerate original row labels and construct their independently proved
pinned witnesses. This need not choose the old permuted witness tables. -/
def splitPinnedTypeClasses (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (defaultValue : Fin d) : List (A × StoredCode d n) :=
  (materializedTypeSearch m W label n 0 (Vector.ofFn (fun _ => defaultValue)) []).1.map
    (fun a => (a,storeCode (pinnedTypeClassCode m W label a defaultValue)))

theorem splitPinnedTypeClasses_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hEq : PreservesRowEquivalence m (labelFiber R label))
    (defaultValue : Fin d) : ∀ entry ∈ splitPinnedTypeClasses m W label defaultValue,
      Correct entry.2.toCode (labelFiber R label entry.1) := by
  intro entry he
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp he
  simpa only [storeCode_toCode] using pinnedTypeClassCode_correct hm hR hW label hEq a defaultValue

/-- Only the label list is identical; no equality of chosen witness tables is
claimed. Exact last-occurrence order is retained. -/
theorem splitPinnedTypeClasses_label_list (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (defaultValue : Fin d) :
    (splitPinnedTypeClasses m W label defaultValue).map Prod.fst =
      (splitTypeClasses m W label defaultValue).map Prod.fst := by
  simp [splitPinnedTypeClasses,splitTypeClasses,List.map_map]

theorem splitPinnedTypeClasses_labels {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hEq : PreservesRowEquivalence m (labelFiber R label))
    (defaultValue : Fin d) (a : A) :
    a ∈ (splitPinnedTypeClasses m W label defaultValue).map Prod.fst ↔
      ∃ x ∈ R, label (Vector.ofFn x) = a := by
  rw [splitPinnedTypeClasses_label_list]
  exact splitTypeClasses_labels hm hR hW label (allTypesPartition_of_row_equivalence hm hEq) defaultValue a

theorem splitPinnedTypeClasses_nodup (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (defaultValue : Fin d) :
    ((splitPinnedTypeClasses m W label defaultValue).map Prod.fst).Nodup := by
  rw [splitPinnedTypeClasses_label_list]
  exact splitTypeClasses_nodup m W label defaultValue

theorem splitPinnedTypeClasses_length_le {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hEq : PreservesRowEquivalence m (labelFiber R label))
    (defaultValue : Fin d) (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U) :
    (splitPinnedTypeClasses m W label defaultValue).length ≤ U.card := by
  simpa only [splitPinnedTypeClasses,List.length_map] using materializedTypeSearch_length_le hm hR hW
    label (allTypesPartition_of_row_equivalence hm hEq).base n 0 (by omega)
    (Vector.ofFn (fun _ => defaultValue)) U hU

end ComplexCSP.MaltsevWitness
