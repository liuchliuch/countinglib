import ComplexCSP.Structure.MaltsevRelations

/-! A constructive witness for a finite common Mal'tsev operation.
Finite Mal'tsev witness functions and materialized reconstruction. -/
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {D : Type*} {n : ℕ}
abbrev Tuple (D : Type*) (n : ℕ) := Vector D n
def view (x : Tuple D n) : Fin n → D := fun i => x[i.val]
@[simp] theorem view_ofFn (x : Fin n → D) : view (Vector.ofFn x) = x := by
  funext i
  simp [view]
theorem view_injective : Function.Injective (@view D n) := by
  intro x y h
  apply Vector.ext
  intro i hi
  exact congrFun h ⟨i, hi⟩
def PrefixEq (k : ℕ) (x y : Fin n → D) : Prop := ∀ i : Fin n, i.val < k → x i = y i
theorem PrefixEq.refl (k : ℕ) (x : Fin n → D) : PrefixEq k x x := fun _ _ => rfl
theorem PrefixEq.symm {k : ℕ} {x y : Fin n → D} (h : PrefixEq k x y) :
    PrefixEq k y x := fun i hi => (h i hi).symm
theorem PrefixEq.trans {k : ℕ} {x y z : Fin n → D}
    (h : PrefixEq k x y) (h' : PrefixEq k y z) : PrefixEq k x z :=
  fun i hi => (h i hi).trans (h' i hi)
theorem PrefixEq.eq {x y : Fin n → D} (h : PrefixEq n x y) : x = y := by
  funext i
  exact h i i.isLt
def Fork (R : Set (Fin n → D)) (i : Fin n) (a b : D) : Prop :=
  ∃ x ∈ R, ∃ y ∈ R, PrefixEq i.val x y ∧ x i = a ∧ y i = b
theorem fork_refl {R : Set (Fin n → D)} {i : Fin n} {x : Fin n → D}
    (hx : x ∈ R) : Fork R i (x i) (x i) :=
  ⟨x, hx, x, hx, PrefixEq.refl _ _, rfl, rfl⟩
theorem fork_symm {R : Set (Fin n → D)} {i : Fin n} {a b : D}
    (h : Fork R i a b) : Fork R i b a := by
  obtain ⟨x, hx, y, hy, hxy, ha, hb⟩ := h
  exact ⟨y, hy, x, hx, hxy.symm, hb, ha⟩
theorem fork_transport {R : Set (Fin n → D)} {m : Operation D}
    (hm : IsMaltsev m) (hR : Preserves m R) {i : Fin n} {a b : D}
    (hab : Fork R i a b) {x : Fin n → D} (hx : x ∈ R) (hxi : x i = a) :
    ∃ y ∈ R, PrefixEq i.val x y ∧ y i = b := by
  obtain ⟨u, hu, v, hv, huv, hui, hvi⟩ := hab
  refine ⟨map₃ m x u v, hR x hx u hu v hv, ?_, ?_⟩
  · intro j hj
    simp only [map₃, huv j hj]
    exact (hm.1 _ _).symm
  · simp only [map₃, hxi, hui, hvi]
    exact hm.2 _ _
theorem fork_trans {R : Set (Fin n → D)} {m : Operation D}
    (hm : IsMaltsev m) (hR : Preserves m R) {i : Fin n} {a b c : D}
    (hab : Fork R i a b) (hbc : Fork R i b c) : Fork R i a c := by
  obtain ⟨x, hx, y, hy, hxy, hxa, hyb⟩ := hab
  obtain ⟨z, hz, hyz, hzc⟩ := fork_transport hm hR hbc hy hyb
  exact ⟨x, hx, z, hz, hxy.trans hyz, hxa, hzc⟩
structure Code (D : Type*) (n : ℕ) where
  seed : Option (Tuple D n)
  lookup : Fin n → D → Option (Tuple D n)
structure Correct (W : Code D n) (R : Set (Fin n → D)) : Prop where
  seed_sound : ∀ x, W.seed = some x → view x ∈ R
  seed_complete : R.Nonempty → ∃ x, W.seed = some x
  lookup_sound : ∀ i a x, W.lookup i a = some x → view x ∈ R ∧ view x i = a
  lookup_complete : ∀ i x, x ∈ R → ∃ y, W.lookup i (x i) = some y
  coherent : ∀ i a b x y, Fork R i a b → W.lookup i a = some x → W.lookup i b = some y →
    PrefixEq i.val (view x) (view y)
variable [DecidableEq D]
def repair (m : Operation D) (W : Code D n) (i : Fin n)
    (target current : Tuple D n) : Option (Tuple D n) := do
  let u ← W.lookup i (view current i)
  let v ← W.lookup i (view target i)
  if ∀ j : Fin n, j.val < i.val → view u j = view v j then
    return Vector.ofFn (map₃ m (view current) (view u) (view v))
  else none
def reconstructTo (m : Operation D) (W : Code D n) (target : Tuple D n) :
    ℕ → Option (Tuple D n)
  | 0 => W.seed
  | k + 1 => if h : k < n then do
      let current ← reconstructTo m W target k
      repair m W ⟨k, h⟩ target current
    else reconstructTo m W target k
def member (m : Operation D) (W : Code D n) (target : Tuple D n) : Bool :=
  match reconstructTo m W target n with
  | none => false
  | some x => decide (x = target)
theorem repair_sound {R : Set (Fin n → D)} {m : Operation D}
    (hR : Preserves m R) {W : Code D n} (hW : Correct W R)
    {i : Fin n} {target current result : Tuple D n} (hc : view current ∈ R)
    (h : repair m W i target current = some result) : view result ∈ R := by
  unfold repair at h
  cases hu : W.lookup i (view current i) with
  | none => simp [hu] at h
  | some u =>
    cases hv : W.lookup i (view target i) with
    | none => simp [hu, hv] at h
    | some v =>
      simp only [hu, hv] at h
      dsimp only [Bind.bind, Option.bind] at h
      split at h
      · have heq : Vector.ofFn (map₃ m (view current) (view u) (view v)) = result := Option.some.inj h
        rw [← heq, view_ofFn]
        exact hR _ hc _ (hW.lookup_sound _ _ _ hu).1 _ (hW.lookup_sound _ _ _ hv).1
      · contradiction
theorem repair_complete {R : Set (Fin n → D)} {m : Operation D}
    (hm : IsMaltsev m) {W : Code D n} (hW : Correct W R)
    {i : Fin n} {target current : Tuple D n} (ht : view target ∈ R) (hc : view current ∈ R)
    (hpre : PrefixEq i.val (view current) (view target)) :
    ∃ result, repair m W i target current = some result ∧
      PrefixEq (i.val + 1) (view result) (view target) := by
  obtain ⟨u, hu⟩ := hW.lookup_complete i (view current) hc
  obtain ⟨v, hv⟩ := hW.lookup_complete i (view target) ht
  have hf : Fork R i (view current i) (view target i) := ⟨view current, hc, view target, ht, hpre, rfl, rfl⟩
  have hp := hW.coherent _ _ _ _ _ hf hu hv
  refine ⟨Vector.ofFn (map₃ m (view current) (view u) (view v)), ?_, ?_⟩
  · simp only [repair, hu, hv]
    dsimp only [Bind.bind, Option.bind]
    rw [if_pos (show ∀ j : Fin n, j.val < i.val → view u j = view v j from hp)]
    rfl
  · rw [view_ofFn]
    intro j hj
    by_cases hji : j.val < i.val
    · simp only [map₃, hp j hji, hm.1]
      exact hpre j hji
    · have hji : j = i := Fin.ext (by omega)
      subst j
      simp only [map₃, (hW.lookup_sound _ _ _ hu).2, (hW.lookup_sound _ _ _ hv).2]
      exact hm.2 _ _
theorem reconstructTo_sound {R : Set (Fin n → D)} {m : Operation D}
    (hR : Preserves m R) {W : Code D n} (hW : Correct W R)
    (target : Tuple D n) (k : ℕ) {result : Tuple D n}
    (h : reconstructTo m W target k = some result) : view result ∈ R := by
  induction k generalizing result with
  | zero => exact hW.seed_sound _ h
  | succ k ih =>
    simp only [reconstructTo] at h
    split at h
    · cases he : reconstructTo m W target k with
      | none => simp [he] at h
      | some current =>
        simp only [he] at h
        exact repair_sound hR hW (ih he) h
    · exact ih h
theorem reconstructTo_complete {R : Set (Fin n → D)} {m : Operation D}
    (hm : IsMaltsev m) (hR : Preserves m R) {W : Code D n} (hW : Correct W R)
    (target : Tuple D n) (ht : view target ∈ R) (k : ℕ) (hk : k ≤ n) :
    ∃ result, reconstructTo m W target k = some result ∧ PrefixEq k (view result) (view target) := by
  induction k with
  | zero =>
    obtain ⟨x, hx⟩ := hW.seed_complete ⟨view target, ht⟩
    exact ⟨x, hx, by intro i hi; omega⟩
  | succ k ih =>
    obtain ⟨current, hc, hpre⟩ := ih (by omega)
    have hk' : k < n := by omega
    obtain ⟨result, hr, hp⟩ := repair_complete hm hW ht
      (reconstructTo_sound hR hW target k hc) (i := ⟨k, hk'⟩) hpre
    exact ⟨result, by simp [reconstructTo, hk', hc, hr], hp⟩
theorem member_correct {R : Set (Fin n → D)} {m : Operation D}
    (hm : IsMaltsev m) (hR : Preserves m R) {W : Code D n} (hW : Correct W R)
    (target : Tuple D n) : member m W target = true ↔ view target ∈ R := by
  constructor
  · intro h
    unfold member at h
    cases he : reconstructTo m W target n with
    | none => simp [he] at h
    | some result =>
      have hr : result = target := by simpa [he] using h
      subst result
      exact reconstructTo_sound hR hW target n he
  · intro ht
    obtain ⟨result, hr, hp⟩ := reconstructTo_complete hm hR hW target ht n le_rfl
    have he : result = target := view_injective hp.eq
    simp [member, hr, he]
end ComplexCSP.MaltsevWitness
