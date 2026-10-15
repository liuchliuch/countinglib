import ComplexCSP.Structure.MaltsevTypeWitness

/-! # Computed type witnesses with one coordinate prescribed -/
set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ} {A : Type*} [DecidableEq A]

@[simp] theorem projectTuple_inverse (π : Equiv.Perm (Fin n)) (x : Tuple (Fin d) n) :
    projectTuple π.symm (projectTuple π x) = x := by
  apply view_injective
  funext i
  simp [projectTuple, Function.comp_def]

@[simp] theorem coordinateImage_refl (R : Set (Fin n → Fin d)) :
    coordinateImage R (Equiv.refl (Fin n)) = R := by
  ext x
  simp [coordinateImage]

theorem coordinateImage_equiv (R : Set (Fin n → Fin d)) (π : Equiv.Perm (Fin n))
    (x : Fin n → Fin d) : x ∈ coordinateImage R π ↔ x ∘ π.symm ∈ R := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [Function.comp_def] using hy
  · intro hx
    exact ⟨x ∘ π.symm, hx, by funext i; simp⟩

def permutedLabel (π : Equiv.Perm (Fin n)) (label : Tuple (Fin d) n → A) : Tuple (Fin d) n → A :=
  fun x => label (projectTuple π.symm x)

def AllTypesPartition (R : Set (Fin n → Fin d)) (label : Tuple (Fin d) n → A) : Prop :=
  ∀ π : Equiv.Perm (Fin n), TypesPartition (coordinateImage R π) (permutedLabel π label)

omit [DecidableEq A] in
theorem AllTypesPartition.base {R : Set (Fin n → Fin d)} {label : Tuple (Fin d) n → A}
    (h : AllTypesPartition R label) : TypesPartition R label := by
  have he : permutedLabel (Equiv.refl (Fin n)) label = label := by
    funext x
    simp [permutedLabel, projectTuple]
  simpa only [coordinateImage_refl, he] using h (Equiv.refl _)

def labelFiber (R : Set (Fin n → Fin d)) (label : Tuple (Fin d) n → A) (wanted : A) :
    Set (Fin n → Fin d) := {x | x ∈ R ∧ label (Vector.ofFn x) = wanted}

def frontIndex (i : Fin n) : Fin n := ⟨0, by have := i.isLt; omega⟩
def frontSwap (i : Fin n) : Equiv.Perm (Fin n) := Equiv.swap (frontIndex i) i

@[simp] theorem frontSwap_front (i : Fin n) : frontSwap i (frontIndex i) = i := by simp [frontSwap]
@[simp] theorem frontSwap_inverse (i : Fin n) : (frontSwap i).symm i = frontIndex i := by simp [frontSwap]

def typeCoordinateWitness (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) (a : Fin d) : Option (Tuple (Fin d) n) :=
  let π := frontSwap i
  let V := storeCode (imageCode m W π)
  (labelExtension m V.toCode (permutedLabel π label) wanted (n - 1) 1
    (Vector.ofFn (fun _ => a))).map (projectTuple π.symm)

theorem typeCoordinateWitness_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (wanted : A) (i : Fin n) (a : Fin d) {result : Tuple (Fin d) n}
    (he : typeCoordinateWitness m W label wanted i a = some result) :
    view result ∈ labelFiber R label wanted ∧ view result i = a := by
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp he
  have hV : Correct (storeCode (imageCode m W (frontSwap i))).toCode (coordinateImage R (frontSwap i)) := by
    simpa only [storeCode_toCode] using imageCode_correct hm hR hW (frontSwap i)
  have hdepth : 1 + (n - 1) = n := by have := i.isLt; omega
  obtain ⟨huR, hp, hl⟩ := labelExtension_spec hm (coordinateImage_preserves hR (frontSwap i)) hV
    (permutedLabel (frontSwap i) label) wanted (n - 1) 1 hdepth _ hu
  have hpin := hp (frontIndex i) (by simp [frontIndex])
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simpa only [projectTuple, view_ofFn] using (coordinateImage_equiv R (frontSwap i) (view u)).mp huR
  · simp only [ofFn_view]
    exact hl
  · simpa [projectTuple, Function.comp_def] using hpin

theorem typeCoordinateWitness_complete {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : AllTypesPartition R label)
    (wanted : A) (i : Fin n) (a : Fin d) {x : Fin n → Fin d}
    (hx : x ∈ labelFiber R label wanted) (hxi : x i = a) :
    ∃ result, typeCoordinateWitness m W label wanted i a = some result := by
  let π := frontSwap i
  let V := (storeCode (imageCode m W π)).toCode
  let target : Tuple (Fin d) n := Vector.ofFn (fun _ => a)
  have hV : Correct V (coordinateImage R π) := by
    simpa only [V, storeCode_toCode] using imageCode_correct hm hR hW π
  have hdepth : 1 + (n - 1) = n := by have := i.isLt; omega
  have ht : HasType (coordinateImage R π) (permutedLabel π label) 1 target wanted := by
    refine ⟨x ∘ π, ⟨x, hx.1, rfl⟩, ?_, ?_⟩
    · intro j hj
      have hj0 : j = frontIndex i := Fin.ext (by simp only [frontIndex]; omega)
      subst j
      simpa [target, π] using hxi
    · have heq : Vector.ofFn (x ∘ π) = projectTuple π (Vector.ofFn x) := by simp [projectTuple]
      rw [heq]
      simpa [permutedLabel] using hx.2
  obtain ⟨u, hu⟩ := labelExtension_complete hm (coordinateImage_preserves hR π) hV
    (permutedLabel π label) (hTP π) wanted (n - 1) 1 hdepth target ht
  exact ⟨projectTuple π.symm u, congrArg (Option.map (projectTuple π.symm)) hu⟩

end ComplexCSP.MaltsevWitness
