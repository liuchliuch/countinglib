import ComplexCSP.Structure.MaltsevWitnessPrefix
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {D : Type*} {n : ℕ} [DecidableEq D]
def listedRelation (rows : List (Tuple D n)) : Set (Fin n → D) := {x | ∃ y ∈ rows, view y = x}
def findExtension (rows : List (Tuple D n)) (i : Fin n) (a : D)
    (pre : Tuple D n) : Option (Tuple D n) :=
  rows.find? (fun x => decide ((∀ j : Fin n, j.val < i.val → view pre j = view x j) ∧ view x i = a))
theorem findExtension_spec {rows : List (Tuple D n)} {i : Fin n} {a : D}
    {pre result : Tuple D n} (h : findExtension rows i a pre = some result) :
    result ∈ rows ∧ PrefixEq i.val (view pre) (view result) ∧ view result i = a := by
  have hmem := List.mem_of_find?_eq_some (show rows.find? _ = some result from h)
  have ht := List.find?_some (show rows.find? _ = some result from h)
  simp only [decide_eq_true_eq] at ht
  exact ⟨hmem, ht⟩
theorem findExtension_isSome (rows : List (Tuple D n)) (i : Fin n) (a : D) (pre : Tuple D n) :
    (findExtension rows i a pre).isSome = true ↔
      ∃ x ∈ listedRelation rows, PrefixEq i.val (view pre) x ∧ x i = a := by
  simp only [findExtension, List.find?_isSome, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, hp, hi⟩
    exact ⟨view x, ⟨x, hx, rfl⟩, hp, hi⟩
  · rintro ⟨x, ⟨y, hy, rfl⟩, hp, hi⟩
    exact ⟨y, hy, hp, hi⟩
def findAnchor (rows : List (Tuple D n)) (i : Fin n) (a : D) : Option (Tuple D n) :=
  rows.find? (fun x => (findExtension rows i a x).isSome)
def listCode (rows : List (Tuple D n)) : Code D n where
  seed := rows.head?
  lookup i a := (findAnchor rows i a).bind (findExtension rows i a)
theorem findAnchor_congr {rows : List (Tuple D n)} {m : Operation D}
    (hm : IsMaltsev m) (hR : Preserves m (listedRelation rows))
    {i : Fin n} {a b : D} (hab : Fork (listedRelation rows) i a b) :
    findAnchor rows i a = findAnchor rows i b := by
  have he : ∀ z : Tuple D n,
      (findExtension rows i a z).isSome = (findExtension rows i b z).isSome := by
    intro z
    apply Bool.eq_iff_iff.mpr
    rw [findExtension_isSome, findExtension_isSome]
    constructor
    · rintro ⟨x, hx, hzx, hxa⟩
      obtain ⟨y, hy, hxy, hyb⟩ := fork_transport hm hR hab hx hxa
      exact ⟨y, hy, hzx.trans hxy, hyb⟩
    · rintro ⟨x, hx, hzx, hxb⟩
      obtain ⟨y, hy, hxy, hya⟩ := fork_transport hm hR (fork_symm hab) hx hxb
      exact ⟨y, hy, hzx.trans hxy, hya⟩
  exact congrArg (fun p => rows.find? p) (funext he)
theorem listCode_lookup_spec {rows : List (Tuple D n)} {i : Fin n} {a : D}
    {result : Tuple D n} (h : (listCode rows).lookup i a = some result) :
    ∃ anchor, findAnchor rows i a = some anchor ∧ result ∈ rows ∧
      PrefixEq i.val (view anchor) (view result) ∧ view result i = a := by
  change (findAnchor rows i a).bind (findExtension rows i a) = some result at h
  cases he : findAnchor rows i a with
  | none => simp [he] at h
  | some anchor =>
    simp only [he, Option.bind_some] at h
    exact ⟨anchor, rfl, findExtension_spec h⟩
theorem listCode_correct (rows : List (Tuple D n)) {m : Operation D}
    (hm : IsMaltsev m) (hR : Preserves m (listedRelation rows)) :
    Correct (listCode rows) (listedRelation rows) := by
  constructor
  · intro x hx
    cases rows with
    | nil => simp [listCode] at hx
    | cons y ys =>
      have hy : y = x := Option.some.inj hx
      subst y
      exact ⟨x, List.mem_cons_self, rfl⟩
  · rintro ⟨x, y, hy, _⟩
    cases rows with
    | nil => simp at hy
    | cons z zs => exact ⟨z, rfl⟩
  · intro i a x hx
    obtain ⟨_, _, hxr, _, hxi⟩ := listCode_lookup_spec hx
    exact ⟨⟨x, hxr, rfl⟩, hxi⟩
  · rintro i x ⟨y, hy, rfl⟩
    have he : (findExtension rows i (view y i) y).isSome = true :=
      (findExtension_isSome _ _ _ _).mpr ⟨view y, ⟨y, hy, rfl⟩, PrefixEq.refl _ _, rfl⟩
    have ha : (findAnchor rows i (view y i)).isSome = true :=
      List.find?_isSome.mpr ⟨y, hy, he⟩
    cases hh : findAnchor rows i (view y i) with
    | none => simp [hh] at ha
    | some anchor =>
      have hn := List.find?_some (show rows.find? _ = some anchor from hh)
      cases hx : findExtension rows i (view y i) anchor with
      | none => simp [hx] at hn
      | some result => exact ⟨result, by simp [listCode, hh, hx]⟩
  · intro i a b x y hab hx hy
    obtain ⟨u, hu, _, hux, _⟩ := listCode_lookup_spec hx
    obtain ⟨v, hv, _, hvy, _⟩ := listCode_lookup_spec hy
    have huv : u = v := Option.some.inj (hu.symm.trans ((findAnchor_congr hm hR hab).trans hv))
    subst v
    exact hux.symm.trans hvy
structure StoredCode (d n : ℕ) where
  seed : Option (Tuple (Fin d) n)
  table : Vector (Vector (Option (Tuple (Fin d) n)) d) n
def StoredCode.toCode {d n : ℕ} (W : StoredCode d n) : Code (Fin d) n where
  seed := W.seed
  lookup i a := W.table[i.val][a.val]
def storeCode {d n : ℕ} (W : Code (Fin d) n) : StoredCode d n where
  seed := W.seed
  table := Vector.ofFn (fun i => Vector.ofFn (W.lookup i))
@[simp] theorem storeCode_toCode {d n : ℕ} (W : Code (Fin d) n) : (storeCode W).toCode = W := by
  cases W
  simp only [StoredCode.toCode, storeCode, Vector.getElem_ofFn]
def StoredCode.slots {d n : ℕ} (W : StoredCode d n) : List (Option (Tuple (Fin d) n)) :=
  W.table.toList.flatMap Vector.toList
theorem StoredCode.slots_length {d n : ℕ} (W : StoredCode d n) : W.slots.length = n * d := by
  simp [StoredCode.slots, List.length_flatMap, List.map_const', List.sum_replicate]
def StoredCode.cells {d n : ℕ} (W : StoredCode d n) : ℕ :=
  ((W.seed.toList ++ W.slots.flatMap Option.toList).map (fun x => x.toList.length)).sum
theorem StoredCode.cells_le {d n : ℕ} (W : StoredCode d n) : W.cells ≤ n * (n * d + 1) := by
  have h : ∀ xs : List (Option (Tuple (Fin d) n)), (xs.flatMap Option.toList).length ≤ xs.length := by
    intro xs
    induction xs with
    | nil => simp
    | cons x xs ih =>
      cases x with
      | none => simpa using Nat.le_trans ih (Nat.le_succ xs.length)
      | some x => simpa using Nat.succ_le_succ ih
  have hs : W.seed.toList.length ≤ 1 := by cases W.seed <;> simp
  have ht := h W.slots
  rw [W.slots_length] at ht
  simp only [StoredCode.cells, List.map_append, List.sum_append]
  simp only [Vector.length_toList, List.map_const', List.sum_replicate, smul_eq_mul]
  nlinarith
end ComplexCSP.MaltsevWitness
