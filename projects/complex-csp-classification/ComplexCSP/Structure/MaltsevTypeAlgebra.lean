import ComplexCSP.Structure.MaltsevTypeCoordinates

/-! # The literal row-equivalence polymorphism supplies the splitting hypotheses -/
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ} {A : Type*}

theorem labelFiber_disjoint (R : Set (Fin n → Fin d)) (label : Tuple (Fin d) n → A) :
    DisjointClasses (labelFiber R label) := by
  intro a b x hx hy
  exact hx.2.symm.trans hy.2

theorem row_equivalence_support_preserves {m : Operation (Fin d)}
    {R : Set (Fin n → Fin d)} {label : Tuple (Fin d) n → A}
    (h : PreservesRowEquivalence m (labelFiber R label)) : Preserves m R := by
  intro x hx y hy z hz
  obtain ⟨a, ha, _⟩ := h x x y y z z
    ⟨label (Vector.ofFn x), ⟨hx, rfl⟩, ⟨hx, rfl⟩⟩
    ⟨label (Vector.ofFn y), ⟨hy, rfl⟩, ⟨hy, rfl⟩⟩
    ⟨label (Vector.ofFn z), ⟨hz, rfl⟩, ⟨hz, rfl⟩⟩
  exact ha.1

theorem row_equivalence_fibers_preserves {m : Operation (Fin d)} (hm : IsMaltsev m)
    {R : Set (Fin n → Fin d)} {label : Tuple (Fin d) n → A}
    (h : PreservesRowEquivalence m (labelFiber R label)) (a : A) :
    Preserves m (labelFiber R label a) := by
  intro x hx y hy z hz
  obtain ⟨b, hb, hb'⟩ := h x x y x z x ⟨a, hx, hx⟩ ⟨a, hy, hx⟩ ⟨a, hz, hx⟩
  have he : map₃ m x x x = x := by funext i; exact hm.1 _ _
  rw [he] at hb'
  have hba := labelFiber_disjoint R label b a x hb' hx
  rwa [hba] at hb

theorem permuted_type_eq_rowType (R : Set (Fin n → Fin d)) (label : Tuple (Fin d) n → A)
    (π : Equiv.Perm (Fin n)) (len : ℕ) (hlen : len ≤ n) (target : Tuple (Fin d) n) :
    {a | HasType (coordinateImage R π) (permutedLabel π label) len target a} =
      RowType (labelFiber R label) (fun i : Fin len => π (Fin.castLE hlen i))
        (fun i => view target (Fin.castLE hlen i)) := by
  ext a
  constructor
  · rintro ⟨x, ⟨y, hy, rfl⟩, hp, hl⟩
    have hl' : label (Vector.ofFn y) = a := by
      have he : projectTuple π.symm (Vector.ofFn (y ∘ π)) = Vector.ofFn y := by
        apply view_injective
        funext i
        simp [projectTuple, Function.comp_def]
      simpa only [permutedLabel, he] using hl
    exact ⟨y, ⟨hy, hl'⟩, fun i => hp (Fin.castLE hlen i) i.isLt⟩
  · rintro ⟨y, ⟨hy, hl⟩, hp⟩
    refine ⟨y ∘ π, ⟨y, hy, rfl⟩, ?_, ?_⟩
    · intro j hj
      exact hp ⟨j.val, hj⟩
    · have he : projectTuple π.symm (Vector.ofFn (y ∘ π)) = Vector.ofFn y := by
        apply view_injective
        funext i
        simp [projectTuple, Function.comp_def]
      simpa only [permutedLabel, he] using hl

/-- This is the exact all-coordinate-order Type Partition used by splitting,
derived from the actual common row-equivalence operation. -/
theorem allTypesPartition_of_row_equivalence {m : Operation (Fin d)} (hm : IsMaltsev m)
    {R : Set (Fin n → Fin d)} {label : Tuple (Fin d) n → A}
    (h : PreservesRowEquivalence m (labelFiber R label)) : AllTypesPartition R label := by
  intro π len hlen x y
  rw [permuted_type_eq_rowType R label π len hlen x,
    permuted_type_eq_rowType R label π len hlen y]
  exact row_equivalence_forces_type_partition (labelFiber_disjoint R label) hm h _ _ _

end ComplexCSP.MaltsevWitness
