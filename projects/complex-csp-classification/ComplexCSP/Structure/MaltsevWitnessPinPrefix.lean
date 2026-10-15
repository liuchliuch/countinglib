import ComplexCSP.Structure.MaltsevWitnessPin
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ}
def tailTuple (x : Tuple (Fin d) (n + 1)) : Tuple (Fin d) n := Vector.ofFn (fun i => view x i.succ)
def tailRelation (R : Set (Fin (n + 1) → Fin d)) : Set (Fin n → Fin d) :=
  {x | ∃ y ∈ R, ∀ i, y i.succ = x i}
def tailCode (W : Code (Fin d) (n + 1)) : Code (Fin d) n where
  seed := W.seed.map tailTuple
  lookup i a := (W.lookup i.succ a).map tailTuple
theorem tailRelation_preserves {m : Operation (Fin d)} {R : Set (Fin (n + 1) → Fin d)}
    (hR : Preserves m R) : Preserves m (tailRelation R) := by
  rintro x ⟨x', hx, hxx⟩ y ⟨y', hy, hyy⟩ z ⟨z', hz, hzz⟩
  refine ⟨map₃ m x' y' z', hR _ hx _ hy _ hz, ?_⟩
  intro i
  simp [map₃, hxx, hyy, hzz]
theorem pinnedFirst_preserves {m : Operation (Fin d)} (hm : IsMaltsev m)
    {R : Set (Fin (n + 1) → Fin d)} (hR : Preserves m R) (a : Fin d) : Preserves m (pinnedFirst R a) := by
  intro x hx y hy z hz
  exact ⟨hR _ hx.1 _ hy.1 _ hz.1, by simp [map₃, hx.2, hy.2, hz.2, hm.1]⟩
theorem tailCode_correct {W : Code (Fin d) (n + 1)} {R : Set (Fin (n + 1) → Fin d)}
    (hW : Correct W R) (a : Fin d) (ha : ∀ x ∈ R, x 0 = a) : Correct (tailCode W) (tailRelation R) := by
  constructor
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact ⟨view y, hW.seed_sound y hy, fun i => by simp [tailTuple]⟩
  · rintro ⟨x, y, hy, _⟩
    obtain ⟨z, hz⟩ := hW.seed_complete ⟨y, hy⟩
    exact ⟨tailTuple z, by simp [tailCode, hz]⟩
  · intro i b x hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨hyR, hyi⟩ := hW.lookup_sound _ _ _ hy
    exact ⟨⟨view y, hyR, fun j => by simp [tailTuple]⟩, by simpa [tailTuple] using hyi⟩
  · rintro i x ⟨y, hy, hyx⟩
    obtain ⟨z, hz⟩ := hW.lookup_complete i.succ y hy
    exact ⟨tailTuple z, by simp [tailCode, ← hyx i, hz]⟩
  · intro i b c x y hf hx hy
    obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.mp hx
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hy
    obtain ⟨p, ⟨p', hp', hpp⟩, q, ⟨q', hq', hqq⟩, hpq, hpb, hqc⟩ := hf
    have hf' : Fork R i.succ b c := by
      refine ⟨p', hp', q', hq', ?_, (hpp i).trans hpb, (hqq i).trans hqc⟩
      intro j hj
      cases j using Fin.cases with
      | zero => exact (ha p' hp').trans (ha q' hq').symm
      | succ j => exact (hpp j).trans ((hpq j (by simpa using hj)).trans (hqq j).symm)
    have huv := hW.coherent _ _ _ _ _ hf' hu hv
    intro j hj
    simpa [tailTuple] using huv j.succ (by simpa using hj)
def pinDropCode (m : Operation (Fin d)) (W : Code (Fin d) (n + 1)) (a : Fin d) : Code (Fin d) n :=
  tailCode (pinFirstCode m W a)
theorem pinDropCode_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (n + 1)} {R : Set (Fin (n + 1) → Fin d)}
    (hR : Preserves m R) (hW : Correct W R) (a : Fin d) :
    Correct (pinDropCode m W a) (tailRelation (pinnedFirst R a)) :=
  tailCode_correct (pinFirstCode_correct hm hR hW a) a (fun _ hx => hx.2)
def pinPrefixCode (m : Operation (Fin d)) (out : ℕ) :
    (k : ℕ) → Code (Fin d) (out + k) → Tuple (Fin d) k → Code (Fin d) out
  | 0, W, _ => W
  | k + 1, W, a => pinPrefixCode m out k
      (storeCode (pinDropCode m W (view a 0))).toCode (tailTuple a)
def prefixFiber (out : ℕ) : (k : ℕ) → Set (Fin (out + k) → Fin d) → Tuple (Fin d) k → Set (Fin out → Fin d)
  | 0, R, _ => R
  | k + 1, R, a => prefixFiber out k (tailRelation (pinnedFirst R (view a 0))) (tailTuple a)
theorem pinPrefixCode_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    (out k : ℕ) (W : Code (Fin d) (out + k)) (R : Set (Fin (out + k) → Fin d))
    (hR : Preserves m R) (hW : Correct W R) (a : Tuple (Fin d) k) :
    Correct (pinPrefixCode m out k W a) (prefixFiber out k R a) := by
  induction k with
  | zero => exact hW
  | succ k ih =>
    simp only [pinPrefixCode, prefixFiber, storeCode_toCode]
    exact ih _ _ (tailRelation_preserves (pinnedFirst_preserves hm hR _)) (pinDropCode_correct hm hR hW _) _
theorem prefixFiber_preserves {m : Operation (Fin d)} (hm : IsMaltsev m)
    (out k : ℕ) (R : Set (Fin (out + k) → Fin d)) (hR : Preserves m R) (a : Tuple (Fin d) k) :
    Preserves m (prefixFiber out k R a) := by
  induction k with
  | zero => exact hR
  | succ k ih => exact ih _ (tailRelation_preserves (pinnedFirst_preserves hm hR _)) _
def prependPrefix (out : ℕ) : (k : ℕ) → Tuple (Fin d) k → (Fin out → Fin d) → (Fin (out + k) → Fin d)
  | 0, _, x => x
  | k + 1, a, x => Fin.cons (view a 0) (prependPrefix out k (tailTuple a) x)
theorem mem_prefixFiber (out k : ℕ) (R : Set (Fin (out + k) → Fin d)) (a : Tuple (Fin d) k) (x : Fin out → Fin d) :
    x ∈ prefixFiber out k R a ↔ prependPrefix out k a x ∈ R := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [prefixFiber, ih]
    simp only [tailRelation, pinnedFirst, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨y, ⟨hy, hy0⟩, hyt⟩
      have he : y = prependPrefix out (k + 1) a x := by
        funext i
        cases i using Fin.cases with
        | zero => exact hy0
        | succ i => exact hyt i
      rwa [← he]
    · intro h
      exact ⟨prependPrefix out (k + 1) a x, ⟨h, rfl⟩, fun _ => rfl⟩
end ComplexCSP.MaltsevWitness
