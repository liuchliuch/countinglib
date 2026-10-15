import ComplexCSP.Structure.MaltsevWitnessClosure
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
section Compress
variable {A B : Type*} [DecidableEq B]
def compress (key : A → B) : List A → List A
  | [] => []
  | x :: xs => let ys := compress key xs
      if (ys.map key).contains (key x) then ys else x :: ys
theorem compress_subset (key : A → B) (xs : List A) : compress key xs ⊆ xs := by
  induction xs with
  | nil => simp [compress]
  | cons x xs ih =>
    simp only [compress]
    split
    · exact fun _ h => List.mem_cons_of_mem _ (ih h)
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih hz)
theorem compress_key_mem (key : A → B) (xs : List A) (b : B) :
    b ∈ (compress key xs).map key ↔ b ∈ xs.map key := by
  induction xs generalizing b with
  | nil => simp [compress]
  | cons x xs ih =>
    simp only [compress]
    split
    next hx =>
      have hx' : key x ∈ xs.map key := ih _ |>.mp (List.contains_iff_mem.mp hx)
      simp only [List.map_cons, List.mem_cons]
      rw [ih]
      exact ⟨Or.inr, fun h => h.elim (fun he => he ▸ hx') id⟩
    · simp only [List.map_cons, List.mem_cons, ih]
theorem compress_nodup (key : A → B) (xs : List A) : ((compress key xs).map key).Nodup := by
  induction xs with
  | nil => simp [compress]
  | cons x xs ih =>
    simp only [compress]
    split
    · exact ih
    next hx =>
      simp only [List.map_cons, List.nodup_cons]
      exact ⟨by simpa using hx, ih⟩
end Compress
variable {d n k : ℕ}
def projectionKey (ρ : Fin k → Fin n) (x : Tuple (Fin d) n) : Fin k → Fin d := view x ∘ ρ
def keySet (ρ : Fin k → Fin n) (xs : List (Tuple (Fin d) n)) : Finset (Fin k → Fin d) :=
  (xs.map (projectionKey ρ)).toFinset
theorem mem_keySet (ρ : Fin k → Fin n) (xs : List (Tuple (Fin d) n)) (a : Fin k → Fin d) :
    a ∈ keySet ρ xs ↔ ∃ x ∈ xs, projectionKey ρ x = a := by simp [keySet]
theorem keySet_card_le (ρ : Fin k → Fin n) (xs : List (Tuple (Fin d) n)) :
    (keySet ρ xs).card ≤ d ^ k := by simpa using (keySet ρ xs).card_le_univ
@[simp] theorem keySet_compress (ρ : Fin k → Fin n) (xs : List (Tuple (Fin d) n)) :
    keySet ρ (compress (projectionKey ρ) xs) = keySet ρ xs := by
  ext a
  simp only [keySet, List.mem_toFinset]
  exact compress_key_mem _ _ _
theorem compress_length_le (ρ : Fin k → Fin n) (xs : List (Tuple (Fin d) n)) :
    (compress (projectionKey ρ) xs).length ≤ d ^ k := by
  simpa using (compress_nodup (projectionKey ρ) xs).length_le_card
def tripleRows (m : Operation (Fin d)) (xs : List (Tuple (Fin d) n)) : List (Tuple (Fin d) n) :=
  xs.flatMap fun x => xs.flatMap fun y => xs.map fun z => Vector.ofFn (map₃ m (view x) (view y) (view z))
theorem mem_tripleRows (m : Operation (Fin d)) (xs : List (Tuple (Fin d) n)) (v : Tuple (Fin d) n) :
    v ∈ tripleRows m xs ↔ ∃ x ∈ xs, ∃ y ∈ xs, ∃ z ∈ xs,
      Vector.ofFn (map₃ m (view x) (view y) (view z)) = v := by simp [tripleRows, List.mem_flatMap]
def closureStep (m : Operation (Fin d)) (ρ : Fin k → Fin n)
    (xs : List (Tuple (Fin d) n)) : List (Tuple (Fin d) n) :=
  compress (projectionKey ρ) (xs ++ tripleRows m xs)
theorem keySet_subset_step (m : Operation (Fin d)) (ρ : Fin k → Fin n) (xs : List (Tuple (Fin d) n)) :
    keySet ρ xs ⊆ keySet ρ (closureStep m ρ xs) := by
  rw [closureStep, keySet_compress]
  intro a ha
  obtain ⟨x, hx, rfl⟩ := (mem_keySet _ _ _).mp ha
  exact (mem_keySet _ _ _).mpr ⟨x, List.mem_append_left _ hx, rfl⟩
theorem step_preserves {m : Operation (Fin d)} {R : Set (Fin n → Fin d)}
    (hR : Preserves m R) (ρ : Fin k → Fin n) (xs : List (Tuple (Fin d) n))
    (hx : ∀ x ∈ xs, view x ∈ R) : ∀ x ∈ closureStep m ρ xs, view x ∈ R := by
  intro x h
  have h' := compress_subset (projectionKey ρ) _ h
  rcases List.mem_append.mp h' with h | h
  · exact hx _ h
  · obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := (mem_tripleRows _ _ _).mp h
    simpa using hR _ (hx _ ha) _ (hx _ hb) _ (hx _ hc)
theorem stableKeySet_preserves {m : Operation (Fin d)} (ρ : Fin k → Fin n)
    (xs : List (Tuple (Fin d) n)) (he : keySet ρ (closureStep m ρ xs) = keySet ρ xs) :
    Preserves m (keySet ρ xs : Set (Fin k → Fin d)) := by
  intro a ha b hb c hc
  obtain ⟨x, hx, rfl⟩ := (mem_keySet _ _ _).mp ha
  obtain ⟨y, hy, rfl⟩ := (mem_keySet _ _ _).mp hb
  obtain ⟨z, hz, rfl⟩ := (mem_keySet _ _ _).mp hc
  rw [← he, closureStep, keySet_compress]
  apply (mem_keySet _ _ _).mpr
  refine ⟨Vector.ofFn (map₃ m (view x) (view y) (view z)), ?_, ?_⟩
  · exact List.mem_append_right _ ((mem_tripleRows _ _ _).mpr ⟨x, hx, y, hy, z, hz, rfl⟩)
  · simp only [projectionKey, view_ofFn]
    rfl
def saturate (m : Operation (Fin d)) (ρ : Fin k → Fin n) : ℕ → List (Tuple (Fin d) n) → List (Tuple (Fin d) n)
  | 0, xs => xs
  | fuel + 1, xs =>
    let ys := closureStep m ρ xs
    if keySet ρ ys = keySet ρ xs then xs else saturate m ρ fuel ys
theorem saturate_preserves {m : Operation (Fin d)} {R : Set (Fin n → Fin d)}
    (hR : Preserves m R) (ρ : Fin k → Fin n) (fuel : ℕ)
    (xs : List (Tuple (Fin d) n)) (hx : ∀ x ∈ xs, view x ∈ R) :
    ∀ x ∈ saturate m ρ fuel xs, view x ∈ R := by
  induction fuel generalizing xs with
  | zero => exact hx
  | succ fuel ih =>
    simp only [saturate]
    split
    · exact hx
    · exact ih _ (step_preserves hR ρ xs hx)
theorem keySet_subset_saturate (m : Operation (Fin d)) (ρ : Fin k → Fin n)
    (fuel : ℕ) (xs : List (Tuple (Fin d) n)) : keySet ρ xs ⊆ keySet ρ (saturate m ρ fuel xs) := by
  induction fuel generalizing xs with
  | zero => exact Finset.Subset.refl _
  | succ fuel ih =>
    simp only [saturate]
    split
    · exact Finset.Subset.refl _
    · exact Finset.Subset.trans (keySet_subset_step m ρ xs) (ih _)
theorem saturate_closed (m : Operation (Fin d)) (ρ : Fin k → Fin n)
    (fuel : ℕ) (xs : List (Tuple (Fin d) n)) (hfuel : d ^ k ≤ fuel + (keySet ρ xs).card) :
    Preserves m (keySet ρ (saturate m ρ fuel xs) : Set (Fin k → Fin d)) := by
  induction fuel generalizing xs with
  | zero =>
    have hfull : keySet ρ xs = Finset.univ := by
      apply Finset.eq_univ_of_card
      have hc := keySet_card_le ρ xs
      simpa using (show (keySet ρ xs).card = d ^ k by omega)
    simpa only [saturate, hfull, Finset.coe_univ] using
      (show Preserves m (Set.univ : Set (Fin k → Fin d)) from fun _ _ _ _ _ _ => Set.mem_univ _)
  | succ fuel ih =>
    simp only [saturate]
    split
    next he => exact stableKeySet_preserves ρ xs he
    next he =>
      apply ih
      have hss : keySet ρ xs ⊂ keySet ρ (closureStep m ρ xs) :=
        (keySet_subset_step m ρ xs).ssubset_of_ne (Ne.symm he)
      have hc := Finset.card_lt_card hss
      omega
def projectedClosure (m : Operation (Fin d)) (ρ : Fin k → Fin n)
    (xs : List (Tuple (Fin d) n)) : List (Tuple (Fin d) n) :=
  saturate m ρ (d ^ k) (compress (projectionKey ρ) xs)
theorem saturate_length_le (m : Operation (Fin d)) (ρ : Fin k → Fin n)
    (fuel : ℕ) (xs : List (Tuple (Fin d) n)) (hx : xs.length ≤ d ^ k) :
    (saturate m ρ fuel xs).length ≤ d ^ k := by
  induction fuel generalizing xs with
  | zero => exact hx
  | succ fuel ih =>
    simp only [saturate]
    split
    · exact hx
    · exact ih _ (compress_length_le _ _)
theorem projectedClosure_length_le (m : Operation (Fin d)) (ρ : Fin k → Fin n)
    (xs : List (Tuple (Fin d) n)) : (projectedClosure m ρ xs).length ≤ d ^ k :=
  saturate_length_le _ _ _ _ (compress_length_le _ _)
theorem projectedClosure_sound (m : Operation (Fin d)) (ρ : Fin k → Fin n)
    (xs : List (Tuple (Fin d) n)) {x : Tuple (Fin d) n} (hx : x ∈ projectedClosure m ρ xs) :
    Closure m (listedRelation xs) (view x) := by
  apply saturate_preserves (closure_preserves m (listedRelation xs)) ρ (d ^ k) _ ?_ x hx
  intro y hy
  exact Closure.base ⟨y, compress_subset _ _ hy, rfl⟩
theorem projectedClosure_complete (m : Operation (Fin d)) (ρ : Fin k → Fin n)
    (xs : List (Tuple (Fin d) n)) {x : Fin n → Fin d} (hx : Closure m (listedRelation xs) x) :
    ∃ y ∈ projectedClosure m ρ xs, projectionKey ρ y = x ∘ ρ := by
  have hclosed : Preserves m (keySet ρ (projectedClosure m ρ xs) : Set (Fin k → Fin d)) :=
    saturate_closed _ _ _ _ (by omega)
  have hbase : keySet ρ xs ⊆ keySet ρ (projectedClosure m ρ xs) := by
    have h := keySet_subset_saturate m ρ (d ^ k) (compress (projectionKey ρ) xs)
    simp only [keySet_compress] at h
    exact h
  apply (mem_keySet _ _ _).mp
  induction hx with
  | base hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact hbase ((mem_keySet _ _ _).mpr ⟨y, hy, rfl⟩)
  | combine hx hy hz ihx ihy ihz => exact hclosed _ ihx _ ihy _ ihz
theorem projectedClosure_witnesses {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)}
    (hR : Preserves m R) (hW : Correct W R) (ρ : Fin k → Fin n) :
    (∀ y ∈ projectedClosure m ρ (storedRows W), view y ∈ R) ∧
    (∀ x ∈ R, ∃ y ∈ projectedClosure m ρ (storedRows W), projectionKey ρ y = x ∘ ρ) := by
  have hgen : {x | Closure m (listedRelation (storedRows W)) x} = R := by
    rw [listed_storedRows]
    exact witness_generates hm hR hW
  constructor
  · intro y hy
    rw [← hgen]
    exact projectedClosure_sound _ _ _ hy
  · intro x hx
    apply projectedClosure_complete
    rwa [← hgen] at hx
end ComplexCSP.MaltsevWitness
