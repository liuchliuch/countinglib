import ComplexCSP.Structure.MaltsevWitness
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {D : Type*} {n : ℕ} [DecidableEq D]
theorem repair_target_congr (m : Operation D) (W : Code D n) (i : Fin n)
    (x y current : Tuple D n) (h : view x i = view y i) :
    repair m W i x current = repair m W i y current := by simp only [repair, h]
theorem reconstructTo_target_congr (m : Operation D) (W : Code D n)
    (x y : Tuple D n) (k : ℕ) (h : PrefixEq k (view x) (view y)) :
    reconstructTo m W x k = reconstructTo m W y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [reconstructTo]
    by_cases hk : k < n
    · simp only [dif_pos hk]
      rw [ih (fun j hj => h j (by omega))]
      congr 1
      funext current
      exact repair_target_congr _ _ _ _ _ _ (h ⟨k, hk⟩ (by simp))
    · simp only [dif_neg hk]
      exact ih (fun j hj => h j (by omega))
theorem repair_prefix {R : Set (Fin n → D)} {m : Operation D}
    (hm : IsMaltsev m) {W : Code D n} (hW : Correct W R)
    {i : Fin n} {target current result : Tuple D n}
    (hp : PrefixEq i.val (view current) (view target))
    (h : repair m W i target current = some result) : PrefixEq (i.val + 1) (view result) (view target) := by
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
      next huv =>
        have heq := Option.some.inj h
        rw [← heq, view_ofFn]
        intro j hj
        by_cases hji : j.val < i.val
        · simp only [map₃, huv j hji, hm.1]
          exact hp j hji
        · have hji : j = i := Fin.ext (by omega)
          subst j
          simp only [map₃, (hW.lookup_sound _ _ _ hu).2, (hW.lookup_sound _ _ _ hv).2]
          exact hm.2 _ _
      · contradiction
theorem reconstructTo_prefix {R : Set (Fin n → D)} {m : Operation D}
    (hm : IsMaltsev m) {W : Code D n} (hW : Correct W R)
    (target : Tuple D n) (k : ℕ) (hk : k ≤ n) {result : Tuple D n}
    (h : reconstructTo m W target k = some result) : PrefixEq k (view result) (view target) := by
  induction k generalizing result with
  | zero => intro i hi; omega
  | succ k ih =>
    have hk' : k < n := by omega
    simp only [reconstructTo, dif_pos hk'] at h
    cases he : reconstructTo m W target k with
    | none => simp [he] at h
    | some current =>
      simp only [he] at h
      exact repair_prefix hm hW (ih (by omega) he) h
theorem reconstructTo_isSome_iff {R : Set (Fin n → D)} {m : Operation D}
    (hm : IsMaltsev m) (hR : Preserves m R) {W : Code D n} (hW : Correct W R)
    (target : Tuple D n) (k : ℕ) (hk : k ≤ n) :
    (reconstructTo m W target k).isSome = true ↔ ∃ x ∈ R, PrefixEq k x (view target) := by
  constructor
  · intro h
    cases he : reconstructTo m W target k with
    | none => simp [he] at h
    | some result => exact ⟨view result, reconstructTo_sound hR hW target k he,
        reconstructTo_prefix hm hW target k hk he⟩
  · rintro ⟨x, hx, hp⟩
    let tx : Tuple D n := Vector.ofFn x
    have hv : view tx = x := view_ofFn x
    obtain ⟨result, hr, _⟩ := reconstructTo_complete hm hR hW tx (by simpa [hv] using hx) k hk
    have hcongr := reconstructTo_target_congr m W tx target k (by simpa [hv] using hp)
    rw [hcongr] at hr
    simp [hr]
def projectCode (W : Code D n) (k : ℕ) (hk : k ≤ n) : Code D k where
  seed := W.seed.map (fun x => Vector.ofFn (fun i => view x (Fin.castLE hk i)))
  lookup i a := (W.lookup (Fin.castLE hk i) a).map
    (fun x => Vector.ofFn (fun j => view x (Fin.castLE hk j)))
def projection (R : Set (Fin n → D)) (k : ℕ) (hk : k ≤ n) : Set (Fin k → D) :=
  {x | ∃ y ∈ R, ∀ i, y (Fin.castLE hk i) = x i}
omit [DecidableEq D] in
theorem projectCode_correct {W : Code D n} {R : Set (Fin n → D)}
    (hW : Correct W R) (k : ℕ) (hk : k ≤ n) : Correct (projectCode W k hk) (projection R k hk) := by
  constructor
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact ⟨view y, hW.seed_sound y hy, fun i => by simp⟩
  · rintro ⟨x, y, hy, _⟩
    obtain ⟨z, hz⟩ := hW.seed_complete ⟨y, hy⟩
    exact ⟨Vector.ofFn (fun i => view z (Fin.castLE hk i)), by simp [projectCode, hz]⟩
  · intro i a x hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨hyR, hyi⟩ := hW.lookup_sound _ _ _ hy
    exact ⟨⟨view y, hyR, fun j => by simp⟩, by simpa using hyi⟩
  · rintro i x ⟨y, hy, hxy⟩
    obtain ⟨z, hz⟩ := hW.lookup_complete (Fin.castLE hk i) y hy
    exact ⟨Vector.ofFn (fun j => view z (Fin.castLE hk j)), by simp [projectCode, ← hxy i, hz]⟩
  · intro i a b x y hf hx hy
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hy
    obtain ⟨p, ⟨p', hp', hpp⟩, q, ⟨q', hq', hqq⟩, hpq, hpa, hqb⟩ := hf
    have hf' : Fork R (Fin.castLE hk i) a b := by
      refine ⟨p', hp', q', hq', ?_, (hpp i).trans hpa, (hqq i).trans hqb⟩
      intro j hj
      have hjk : j.val < k := lt_of_lt_of_le hj (Nat.le_of_lt i.isLt)
      have hjp := hpp ⟨j.val, hjk⟩
      have hjq := hqq ⟨j.val, hjk⟩
      exact hjp.trans ((hpq ⟨j.val, hjk⟩ hj).trans hjq.symm)
    have huv := hW.coherent _ _ _ _ _ hf' hu hv
    intro j hj
    simpa using huv (Fin.castLE hk j) hj
end ComplexCSP.MaltsevWitness
