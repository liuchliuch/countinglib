import ComplexCSP.Structure.MaltsevWitnessConstruction
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {D : Type*} {n : ℕ}
inductive Closure (m : Operation D) (S : Set (Fin n → D)) : (Fin n → D) → Prop
  | base {x} : x ∈ S → Closure m S x
  | combine {x y z} : Closure m S x → Closure m S y → Closure m S z → Closure m S (map₃ m x y z)
theorem closure_preserves (m : Operation D) (S : Set (Fin n → D)) :
    Preserves m {x | Closure m S x} := fun _ hx _ hy _ hz => .combine hx hy hz
theorem closure_le {m : Operation D} {S R : Set (Fin n → D)}
    (hS : S ⊆ R) (hR : Preserves m R) {x} (h : Closure m S x) : x ∈ R := by
  induction h with
  | base h => exact hS h
  | combine _ _ _ hx hy hz => exact hR _ hx _ hy _ hz
def storedRelation (W : Code D n) : Set (Fin n → D) :=
  {x | (∃ y, W.seed = some y ∧ view y = x) ∨ ∃ i a y, W.lookup i a = some y ∧ view y = x}
theorem storedRelation_subset {W : Code D n} {R : Set (Fin n → D)}
    (hW : Correct W R) : storedRelation W ⊆ R := by
  rintro x (⟨y, hy, rfl⟩ | ⟨i, a, y, hy, rfl⟩)
  · exact hW.seed_sound _ hy
  · exact (hW.lookup_sound _ _ _ hy).1
theorem witness_generates [DecidableEq D] {W : Code D n} {R : Set (Fin n → D)}
    {m : Operation D} (hm : IsMaltsev m) (hR : Preserves m R) (hW : Correct W R) :
    {x | Closure m (storedRelation W) x} = R := by
  let C : Set (Fin n → D) := {x | Closure m (storedRelation W) x}
  have hCR : C ⊆ R := fun _ h => closure_le (storedRelation_subset hW) hR h
  have hWC : Correct W C := by
    constructor
    · intro x hx
      exact Closure.base (Or.inl ⟨x, hx, rfl⟩)
    · intro hC
      exact hW.seed_complete (hC.mono hCR)
    · intro i a x hx
      exact ⟨Closure.base (Or.inr ⟨i, a, x, hx, rfl⟩), (hW.lookup_sound _ _ _ hx).2⟩
    · intro i x hx
      exact hW.lookup_complete i x (hCR hx)
    · intro i a b x y hf hx hy
      obtain ⟨u, hu, v, hv, huv, hua, hvb⟩ := hf
      exact hW.coherent i a b x y ⟨u, hCR hu, v, hCR hv, huv, hua, hvb⟩ hx hy
  apply Set.Subset.antisymm hCR
  intro x hx
  let t : Tuple D n := Vector.ofFn x
  have hv : view t = x := view_ofFn x
  have hmemb := (member_correct hm hR hW t).mpr (by simpa [hv] using hx)
  have hc := (member_correct hm (closure_preserves m (storedRelation W)) hWC t).mp hmemb
  simp only [hv] at hc
  exact hc
def storedRows {d n : ℕ} (W : Code (Fin d) n) : List (Tuple (Fin d) n) :=
  W.seed.toList ++ (List.ofFn (fun i => (List.ofFn (W.lookup i)).flatMap Option.toList)).flatten
theorem listed_storedRows {d n : ℕ} (W : Code (Fin d) n) :
    listedRelation (storedRows W) = storedRelation W := by
  have hmem : ∀ y, y ∈ storedRows W ↔ W.seed = some y ∨ ∃ i a, W.lookup i a = some y := by
    intro y
    simp [storedRows, List.mem_flatten, List.mem_flatMap, List.mem_ofFn]
  ext x
  simp only [listedRelation, storedRelation, Set.mem_ofPred_eq, hmem]
  constructor
  · rintro ⟨y, (hy | ⟨i, a, hy⟩), hyx⟩
    · exact Or.inl ⟨y, hy, hyx⟩
    · exact Or.inr ⟨i, a, y, hy, hyx⟩
  · rintro (⟨y, hy, hyx⟩ | ⟨i, a, y, hy, hyx⟩)
    · exact ⟨y, Or.inl hy, hyx⟩
    · exact ⟨y, Or.inr ⟨i, a, hy⟩, hyx⟩
end ComplexCSP.MaltsevWitness
