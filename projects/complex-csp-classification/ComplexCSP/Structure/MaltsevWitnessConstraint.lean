import ComplexCSP.Structure.MaltsevWitnessPrefixClosure
set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n r : ℕ}
def consTuple (a : Fin d) (x : Tuple (Fin d) n) : Tuple (Fin d) (n + 1) :=
  Vector.ofFn (Fin.cons a (view x))
def prefixFrame (m : Operation (Fin d)) : {n : ℕ} → Code (Fin d) n → Tuple (Fin d) n → ℕ → List (Tuple (Fin d) n)
  | _, W, _, 0 => storedRows W
  | 0, W, _, _ + 1 => storedRows W
  | _ + 1, W, target, k + 1 =>
    let U := storeCode (pinDropCode m W (view target 0))
    (prefixFrame m U.toCode (tailTuple target) k).map (consTuple (view target 0))
theorem cons_map₃ {m : Operation (Fin d)} (hm : IsMaltsev m) (a : Fin d) (x y z : Fin n → Fin d) :
    Fin.cons a (map₃ m x y z) = map₃ m (Fin.cons a x) (Fin.cons a y) (Fin.cons a z) := by
  funext i
  cases i using Fin.cases with
  | zero => exact (hm.1 _ _).symm
  | succ i => rfl
theorem prefixFrame_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    (k : ℕ) (W : Code (Fin d) n) (R : Set (Fin n → Fin d))
    (hR : Preserves m R) (hW : Correct W R) (target : Tuple (Fin d) n) :
    (∀ y ∈ prefixFrame m W target k, view y ∈ R ∧ PrefixEq k (view y) (view target)) ∧
    (∀ x ∈ R, PrefixEq k x (view target) → Closure m (listedRelation (prefixFrame m W target k)) x) := by
  induction k generalizing n with
  | zero =>
    cases n <;> simp only [prefixFrame]
    all_goals
      constructor
      · intro y hy
        exact ⟨storedRelation_subset hW (by rw [← listed_storedRows]; exact ⟨y, hy, rfl⟩),
          by intro i hi; omega⟩
      · intro x hx _
        rw [listed_storedRows]
        rwa [← witness_generates hm hR hW] at hx
  | succ k ih =>
    cases n with
    | zero =>
      simp only [prefixFrame]
      constructor
      · intro y hy
        exact ⟨storedRelation_subset hW (by rw [← listed_storedRows]; exact ⟨y, hy, rfl⟩),
          by intro i; exact Fin.elim0 i⟩
      · intro x hx _
        rw [listed_storedRows]
        rwa [← witness_generates hm hR hW] at hx
    | succ n =>
      let a := view target 0
      let U := (storeCode (pinDropCode m W a)).toCode
      let R' := tailRelation (pinnedFirst R a)
      have hU : Correct U R' := by simpa only [U, storeCode_toCode] using pinDropCode_correct hm hR hW a
      have hR' : Preserves m R' := tailRelation_preserves (pinnedFirst_preserves hm hR a)
      have hi := ih U R' hR' hU (tailTuple target)
      constructor
      · intro y hy
        obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hy
        obtain ⟨hzR, hzp⟩ := hi.1 z hz
        obtain ⟨z', ⟨hz', hz'a⟩, hz'z⟩ := hzR
        have he : z' = Fin.cons a (view z) := by
          funext j
          cases j using Fin.cases with
          | zero => exact hz'a
          | succ j => exact hz'z j
        refine ⟨?_, ?_⟩
        · change view (Vector.ofFn (Fin.cons a (view z))) ∈ R
          rw [view_ofFn, ← he]
          exact hz'
        · intro j hj
          cases j using Fin.cases with
          | zero => simp [consTuple]
          | succ j =>
            have hj' : j.val < k := by simpa using hj
            simpa [consTuple, tailTuple] using hzp j hj'
      · intro x hx hpx
        have hx0 : x 0 = a := hpx 0 (by simp)
        have hxt : Fin.tail x ∈ R' := ⟨x, ⟨hx, hx0⟩, fun _ => rfl⟩
        have hpxt : PrefixEq k (Fin.tail x) (view (tailTuple target)) := by
          intro j hj
          simpa [tailTuple, Fin.tail] using hpx j.succ (by simpa using Nat.succ_lt_succ hj)
        have hcl := hi.2 (Fin.tail x) hxt hpxt
        have hh := Closure.map (fun y : Fin n → Fin d => Fin.cons a y) (cons_map₃ hm a)
          (T := listedRelation (prefixFrame m W target (k + 1))) ?_ hcl
        · have he : Fin.cons a (Fin.tail x) = x := by
            rw [← hx0]
            exact Fin.cons_self_tail x
          simpa only [he] using hh
        · rintro z ⟨t, ht, rfl⟩
          exact ⟨consTuple a t, List.mem_map.mpr ⟨t, ht, rfl⟩, view_ofFn _⟩
def prefixRestriction (R : Set (Fin n → Fin d)) (target : Tuple (Fin d) n) (k : ℕ) : Set (Fin n → Fin d) :=
  {x | x ∈ R ∧ PrefixEq k x (view target)}
theorem prefixRestriction_preserves {m : Operation (Fin d)} (hm : IsMaltsev m)
    {R : Set (Fin n → Fin d)} (hR : Preserves m R) (target : Tuple (Fin d) n) (k : ℕ) :
    Preserves m (prefixRestriction R target k) := by
  intro x hx y hy z hz
  refine ⟨hR _ hx.1 _ hy.1 _ hz.1, ?_⟩
  intro j hj
  simp only [map₃, hx.2 j hj, hy.2 j hj, hz.2 j hj, hm.1]
def constrainedExtensions (m : Operation (Fin d)) (W : Code (Fin d) n)
    (target : Tuple (Fin d) n) (k : ℕ) (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) :
    List (Tuple (Fin d) n) :=
  (projectedClosure m scope (prefixFrame m W target k)).filter (fun x => accept (projectionKey scope x))
theorem constrainedExtensions_sound {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (target : Tuple (Fin d) n) (k : ℕ) (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool)
    {x : Tuple (Fin d) n} (hx : x ∈ constrainedExtensions m W target k scope accept) :
    view x ∈ R ∧ PrefixEq k (view x) (view target) ∧ accept (view x ∘ scope) = true := by
  obtain ⟨hx, ha⟩ := List.mem_filter.mp hx
  have hsub : listedRelation (prefixFrame m W target k) ⊆ prefixRestriction R target k := by
    rintro y ⟨z, hz, rfl⟩
    exact (prefixFrame_spec hm k W R hR hW target).1 z hz
  have hs := closure_le hsub (prefixRestriction_preserves hm hR target k) (projectedClosure_sound m scope _ hx)
  exact ⟨hs.1, hs.2, ha⟩
theorem constrainedExtensions_complete {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (target : Tuple (Fin d) n) (k : ℕ) (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool)
    {x : Fin n → Fin d} (hx : x ∈ R) (hpx : PrefixEq k x (view target)) (ha : accept (x ∘ scope) = true) :
    ∃ y ∈ constrainedExtensions m W target k scope accept, projectionKey scope y = x ∘ scope := by
  have hcl := (prefixFrame_spec hm k W R hR hW target).2 x hx hpx
  obtain ⟨y, hy, he⟩ := projectedClosure_complete m scope _ hcl
  exact ⟨y, List.mem_filter.mpr ⟨hy, by rwa [he]⟩, he⟩
end ComplexCSP.MaltsevWitness
