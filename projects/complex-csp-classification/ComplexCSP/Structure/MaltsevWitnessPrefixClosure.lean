import ComplexCSP.Structure.MaltsevWitnessPinPrefix
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d out k r : ℕ}
theorem prependPrefix_map₃ {m : Operation (Fin d)} (hm : IsMaltsev m)
    (out k : ℕ) (a : Tuple (Fin d) k) (x y z : Fin out → Fin d) :
    prependPrefix out k a (map₃ m x y z) =
      map₃ m (prependPrefix out k a x) (prependPrefix out k a y) (prependPrefix out k a z) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext i
    cases i using Fin.cases with
    | zero => exact (hm.1 _ _).symm
    | succ i => exact congrFun (ih (tailTuple a)) i
theorem prependPrefix_head (out k : ℕ) (a : Tuple (Fin d) k)
    (x : Fin out → Fin d) (i : Fin (out + k)) (hi : i.val < k) :
    prependPrefix out k a x i = view a ⟨i.val, hi⟩ := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases i using Fin.cases with
    | zero => rfl
    | succ i =>
      have hi' : i.val < k := by simpa using hi
      simpa [prependPrefix, tailTuple, view] using ih (tailTuple a) i hi'
theorem Closure.map {n n' : ℕ} {m : Operation (Fin d)}
    {S : Set (Fin n → Fin d)} {T : Set (Fin n' → Fin d)}
    (f : (Fin n → Fin d) → (Fin n' → Fin d))
    (hf : ∀ x y z, f (map₃ m x y z) = map₃ m (f x) (f y) (f z))
    (hbase : ∀ x ∈ S, f x ∈ T) {x} (hx : Closure m S x) : Closure m T (f x) := by
  induction hx with
  | base hx => exact Closure.base (hbase _ hx)
  | combine hx hy hz ihx ihy ihz =>
    rw [hf]
    exact Closure.combine ihx ihy ihz
def prefixImage (R : Set (Fin (out + k) → Fin d)) (a : Tuple (Fin d) k) : Set (Fin (out + k) → Fin d) :=
  {y | ∃ x, y = prependPrefix out k a x ∧ y ∈ R}
theorem prefixImage_preserves {m : Operation (Fin d)} (hm : IsMaltsev m)
    {R : Set (Fin (out + k) → Fin d)} (hR : Preserves m R) (a : Tuple (Fin d) k) :
    Preserves m (prefixImage R a) := by
  rintro x ⟨x', rfl, hx⟩ y ⟨y', rfl, hy⟩ z ⟨z', rfl, hz⟩
  exact ⟨map₃ m x' y' z', (prependPrefix_map₃ hm out k a x' y' z').symm, hR _ hx _ hy _ hz⟩
def liftedPrefixRows (m : Operation (Fin d)) (W : Code (Fin d) (out + k))
    (a : Tuple (Fin d) k) : List (Tuple (Fin d) (out + k)) :=
  (storedRows (pinPrefixCode m out k W a)).map (fun x => Vector.ofFn (prependPrefix out k a (view x)))
def prefixProjectedClosure (m : Operation (Fin d)) (W : Code (Fin d) (out + k))
    (a : Tuple (Fin d) k) (ρ : Fin r → Fin (out + k)) : List (Tuple (Fin d) (out + k)) :=
  projectedClosure m ρ (liftedPrefixRows m W a)
theorem liftedPrefixRows_sound {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (out + k)} {R : Set (Fin (out + k) → Fin d)}
    (hR : Preserves m R) (hW : Correct W R) (a : Tuple (Fin d) k) :
    listedRelation (liftedPrefixRows m W a) ⊆ prefixImage R a := by
  rintro y ⟨z, hz, rfl⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  have hW' := pinPrefixCode_correct hm out k W R hR hW a
  have hx' : view x ∈ prefixFiber out k R a :=
    storedRelation_subset hW' (by rw [← listed_storedRows]; exact ⟨x, hx, rfl⟩)
  simp only [view_ofFn]
  exact ⟨view x, rfl, (mem_prefixFiber out k R a _).mp hx'⟩
theorem liftedPrefixRows_complete {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (out + k)} {R : Set (Fin (out + k) → Fin d)}
    (hR : Preserves m R) (hW : Correct W R) (a : Tuple (Fin d) k)
    {y : Fin (out + k) → Fin d} (hy : y ∈ prefixImage R a) :
    Closure m (listedRelation (liftedPrefixRows m W a)) y := by
  obtain ⟨x, rfl, hx⟩ := hy
  have hW' := pinPrefixCode_correct hm out k W R hR hW a
  have hR' := prefixFiber_preserves hm out k R hR a
  have hgen := witness_generates hm hR' hW'
  have hx' : Closure m (storedRelation (pinPrefixCode m out k W a)) x := by
    have hx' := (mem_prefixFiber out k R a x).mpr hx
    rwa [← hgen] at hx'
  apply Closure.map (prependPrefix out k a) (prependPrefix_map₃ hm out k a) ?_ hx'
  intro z hz
  rw [← listed_storedRows] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨Vector.ofFn (prependPrefix out k a (view t)), ?_, view_ofFn _⟩
  exact List.mem_map.mpr ⟨t, ht, rfl⟩
theorem prefixProjectedClosure_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (out + k)} {R : Set (Fin (out + k) → Fin d)}
    (hR : Preserves m R) (hW : Correct W R) (a : Tuple (Fin d) k) (ρ : Fin r → Fin (out + k)) :
    (∀ y ∈ prefixProjectedClosure m W a ρ, view y ∈ prefixImage R a) ∧
    (∀ x ∈ prefixImage R a, ∃ y ∈ prefixProjectedClosure m W a ρ, projectionKey ρ y = x ∘ ρ) := by
  constructor
  · intro y hy
    exact closure_le (liftedPrefixRows_sound hm hR hW a)
      (prefixImage_preserves hm hR a) (projectedClosure_sound _ _ _ hy)
  · intro x hx
    exact projectedClosure_complete _ _ _ (liftedPrefixRows_complete hm hR hW a hx)
def constraintPrefixRows (m : Operation (Fin d)) (W : Code (Fin d) (out + k))
    (a : Tuple (Fin d) k) (scope : Fin r → Fin (out + k)) (accept : (Fin r → Fin d) → Bool) :
    List (Tuple (Fin d) (out + k)) :=
  (prefixProjectedClosure m W a scope).filter (fun x => accept (projectionKey scope x))
theorem constraintPrefixRows_sound {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (out + k)} {R : Set (Fin (out + k) → Fin d)}
    (hR : Preserves m R) (hW : Correct W R) (a : Tuple (Fin d) k)
    (scope : Fin r → Fin (out + k)) (accept : (Fin r → Fin d) → Bool)
    {x : Tuple (Fin d) (out + k)} (hx : x ∈ constraintPrefixRows m W a scope accept) :
    view x ∈ prefixImage R a ∧ accept (view x ∘ scope) = true := by
  obtain ⟨hx, ha⟩ := List.mem_filter.mp hx
  exact ⟨(prefixProjectedClosure_correct hm hR hW a scope).1 _ hx, ha⟩
theorem constraintPrefixRows_nonempty {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (out + k)} {R : Set (Fin (out + k) → Fin d)}
    (hR : Preserves m R) (hW : Correct W R) (a : Tuple (Fin d) k)
    (scope : Fin r → Fin (out + k)) (accept : (Fin r → Fin d) → Bool) :
    (∃ x, x ∈ constraintPrefixRows m W a scope accept) ↔
      ∃ x ∈ prefixImage R a, accept (x ∘ scope) = true := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨view x, constraintPrefixRows_sound hm hR hW a scope accept hx⟩
  · rintro ⟨x, hx, ha⟩
    obtain ⟨y, hy, he⟩ := (prefixProjectedClosure_correct hm hR hW a scope).2 x hx
    exact ⟨y, List.mem_filter.mpr ⟨hy, by rwa [he]⟩⟩
end ComplexCSP.MaltsevWitness
