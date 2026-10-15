import ComplexCSP.Structure.MaltsevProjectedClosure
import ComplexCSP.Structure.MaltsevWitnessUnion
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ}
def forkTest (W : Code (Fin d) n) (i : Fin n) (a b : Fin d) : Bool :=
  match W.lookup i a, W.lookup i b with
  | some x, some y => decide (∀ j : Fin n, j.val < i.val → view x j = view y j)
  | _, _ => false
theorem forkTest_correct {W : Code (Fin d) n} {R : Set (Fin n → Fin d)}
    (hW : Correct W R) (i : Fin n) (a b : Fin d) : forkTest W i a b = true ↔ Fork R i a b := by
  constructor
  · intro h
    cases hx : W.lookup i a with
    | none => simp [forkTest, hx] at h
    | some x =>
      cases hy : W.lookup i b with
      | none => simp [forkTest, hy] at h
      | some y =>
        have hp : PrefixEq i.val (view x) (view y) := by simpa [forkTest, hx, hy, PrefixEq] using h
        exact ⟨view x, (hW.lookup_sound _ _ _ hx).1, view y, (hW.lookup_sound _ _ _ hy).1,
          hp, (hW.lookup_sound _ _ _ hx).2, (hW.lookup_sound _ _ _ hy).2⟩
  · intro h
    have hf := h
    obtain ⟨u, hu, v, hv, _, hui, hvi⟩ := h
    obtain ⟨x, hx⟩ := hW.lookup_complete i u hu
    obtain ⟨y, hy⟩ := hW.lookup_complete i v hv
    rw [hui] at hx
    rw [hvi] at hy
    have hp := hW.coherent _ _ _ _ _ hf hx hy
    simpa [forkTest, hx, hy, PrefixEq] using hp
def transportCode (m : Operation (Fin d)) (W : Code (Fin d) n)
    (i : Fin n) (z : Tuple (Fin d) n) (a : Fin d) : Option (Tuple (Fin d) n) :=
  repair m W i (replaceCoordinate z i a) z
theorem transportCode_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    {i : Fin n} {z result : Tuple (Fin d) n} {a : Fin d} (hz : view z ∈ R)
    (he : transportCode m W i z a = some result) :
    view result ∈ R ∧ PrefixEq i.val (view z) (view result) ∧ view result i = a := by
  have hp : PrefixEq i.val (view z) (view (replaceCoordinate z i a)) := by
    intro j hj
    have hji : j ≠ i := by intro h; subst j; omega
    simp [replaceCoordinate, hji]
  exact ⟨repair_sound hR hW hz he, (prefix_replace_iff z i a _).mp (repair_prefix hm hW hp he)⟩
theorem transportCode_complete {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    {i : Fin n} {z : Tuple (Fin d) n} {a : Fin d} (hz : view z ∈ R) (hf : Fork R i (view z i) a) :
    ∃ result, transportCode m W i z a = some result := by
  obtain ⟨x, hx, hzx, hxi⟩ := fork_transport hm hR hf hz rfl
  let tx : Tuple (Fin d) n := Vector.ofFn x
  have hv : view tx = x := view_ofFn x
  obtain ⟨result, hr, _⟩ := repair_complete hm hW (i := i) (target := tx) (current := z)
    (by simpa [hv] using hx) hz (by simpa [hv] using hzx)
  refine ⟨result, ?_⟩
  unfold transportCode
  rw [repair_target_congr m W i (replaceCoordinate z i a) tx z (by simp [replaceCoordinate, hv, hxi])]
  exact hr
def pinnedFirst (R : Set (Fin (n + 1) → Fin d)) (a : Fin d) : Set (Fin (n + 1) → Fin d) :=
  {x | x ∈ R ∧ x 0 = a}
def firstPair (i : Fin (n + 1)) : Fin 2 → Fin (n + 1) := ![0, i]
def pinCandidates (m : Operation (Fin d)) (W : Code (Fin d) (n + 1))
    (a : Fin d) (i : Fin (n + 1)) : List (Tuple (Fin d) (n + 1)) :=
  (projectedClosure m (firstPair i) (storedRows W)).filter (fun z => view z 0 == a)
theorem pinCandidates_sound {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (n + 1)} {R : Set (Fin (n + 1) → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    {a : Fin d} {i : Fin (n + 1)} {z : Tuple (Fin d) (n + 1)}
    (hz : z ∈ pinCandidates m W a i) : view z ∈ pinnedFirst R a := by
  obtain ⟨hz, hza⟩ := List.mem_filter.mp hz
  exact ⟨(projectedClosure_witnesses hm hR hW (firstPair i)).1 _ hz, by simpa using hza⟩
theorem pinCandidates_complete {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (n + 1)} {R : Set (Fin (n + 1) → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    {a : Fin d} (i : Fin (n + 1)) {x : Fin (n + 1) → Fin d} (hx : x ∈ pinnedFirst R a) :
    ∃ z ∈ pinCandidates m W a i, view z i = x i := by
  obtain ⟨z, hz, he⟩ := (projectedClosure_witnesses hm hR hW (firstPair i)).2 x hx.1
  have h0 := congrFun he 0
  have hi := congrFun he 1
  simp only [projectionKey, Function.comp_apply, firstPair, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 hi
  exact ⟨z, List.mem_filter.mpr ⟨hz, by simpa [h0] using hx.2⟩, hi⟩
def pinAnchor (m : Operation (Fin d)) (W : Code (Fin d) (n + 1))
    (a : Fin d) (i : Fin (n + 1)) (b : Fin d) : Option (Tuple (Fin d) (n + 1)) :=
  (pinCandidates m W a i).find? (fun z => forkTest W i (view z i) b)
def pinFirstCode (m : Operation (Fin d)) (W : Code (Fin d) (n + 1)) (a : Fin d) : Code (Fin d) (n + 1) where
  seed := W.lookup 0 a
  lookup i b := if i.val = 0 then if b = a then W.lookup 0 a else none
    else (pinAnchor m W a i b).bind (fun z => transportCode m W i z b)
theorem pinAnchor_congr {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (n + 1)} {R : Set (Fin (n + 1) → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    {a b c : Fin d} {i : Fin (n + 1)} (hbc : Fork R i b c) :
    pinAnchor m W a i b = pinAnchor m W a i c := by
  apply congrArg (fun p => (pinCandidates m W a i).find? p)
  funext z
  apply Bool.eq_iff_iff.mpr
  rw [forkTest_correct hW, forkTest_correct hW]
  exact ⟨fun h => fork_trans hm hR h hbc, fun h => fork_trans hm hR h (fork_symm hbc)⟩
theorem pin_lookup_nonzero_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (n + 1)} {R : Set (Fin (n + 1) → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    {a b : Fin d} {i : Fin (n + 1)} (hi : i.val ≠ 0) {result : Tuple (Fin d) (n + 1)}
    (he : (pinFirstCode m W a).lookup i b = some result) :
    ∃ z, pinAnchor m W a i b = some z ∧ view result ∈ pinnedFirst R a ∧
      PrefixEq i.val (view z) (view result) ∧ view result i = b := by
  simp only [pinFirstCode, if_neg hi] at he
  cases hz : pinAnchor m W a i b with
  | none => simp [hz] at he
  | some z =>
    have hmem := List.mem_of_find?_eq_some (show (pinCandidates m W a i).find? _ = some z from hz)
    have hp := pinCandidates_sound hm hR hW hmem
    simp only [hz, Option.bind_some] at he
    obtain ⟨hr, hpre, hri⟩ := transportCode_spec hm hR hW hp.1 he
    refine ⟨z, rfl, ⟨hr, ?_⟩, hpre, hri⟩
    exact (hpre 0 (by change 0 < i.val; omega)).symm.trans hp.2
theorem pinFirstCode_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (n + 1)} {R : Set (Fin (n + 1) → Fin d)}
    (hR : Preserves m R) (hW : Correct W R) (a : Fin d) : Correct (pinFirstCode m W a) (pinnedFirst R a) := by
  constructor
  · intro x hx
    exact hW.lookup_sound 0 a x hx
  · rintro ⟨x, hx, hxa⟩
    simpa [pinFirstCode, hxa] using hW.lookup_complete 0 x hx
  · intro i b x hx
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext hi
      subst i
      by_cases hb : b = a
      · subst b
        simp only [pinFirstCode, Fin.val_zero, ↓reduceIte] at hx
        have h := hW.lookup_sound 0 a x hx
        exact ⟨h, h.2⟩
      · simp [pinFirstCode, hb] at hx
    · obtain ⟨_, _, hxR, _, hxi⟩ := pin_lookup_nonzero_spec hm hR hW hi hx
      exact ⟨hxR, hxi⟩
  · intro i x hx
    by_cases hi : i.val = 0
    · have hi' : i = 0 := Fin.ext hi
      subst i
      obtain ⟨y, hy⟩ := hW.lookup_complete 0 x hx.1
      exact ⟨y, by simpa [pinFirstCode, hx.2] using hy⟩
    · obtain ⟨y, hy, hyi⟩ := pinCandidates_complete hm hR hW i hx
      have hyr := pinCandidates_sound hm hR hW hy
      have hf : forkTest W i (view y i) (x i) = true :=
        (forkTest_correct hW _ _ _).mpr (by rw [← hyi]; exact fork_refl hyr.1)
      have ha : (pinAnchor m W a i (x i)).isSome = true := List.find?_isSome.mpr ⟨y, hy, hf⟩
      cases hz : pinAnchor m W a i (x i) with
      | none => simp [hz] at ha
      | some z =>
        have hmem := List.mem_of_find?_eq_some (show (pinCandidates m W a i).find? _ = some z from hz)
        have hf' := List.find?_some (show (pinCandidates m W a i).find? _ = some z from hz)
        obtain ⟨result, hr⟩ := transportCode_complete hm hR hW
          (pinCandidates_sound hm hR hW hmem).1 ((forkTest_correct hW _ _ _).mp hf')
        exact ⟨result, by simp only [pinFirstCode, if_neg hi, hz, Option.bind_some, hr]⟩
  · intro i b c x y hbc hx hy
    by_cases hi : i.val = 0
    · intro j hj
      omega
    · obtain ⟨u, hu, _, hux, _⟩ := pin_lookup_nonzero_spec hm hR hW hi hx
      obtain ⟨v, hv, _, hvy, _⟩ := pin_lookup_nonzero_spec hm hR hW hi hy
      have hf : Fork R i b c := by
        obtain ⟨s, hs, t, ht, hst, hsb, htc⟩ := hbc
        exact ⟨s, hs.1, t, ht.1, hst, hsb, htc⟩
      have huv : u = v := Option.some.inj (hu.symm.trans ((pinAnchor_congr hm hR hW hf).trans hv))
      subst v
      exact hux.symm.trans hvy
end ComplexCSP.MaltsevWitness
