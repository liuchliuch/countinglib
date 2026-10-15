import ComplexCSP.Structure.MaltsevCSPWitness
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n k : ℕ}
def coordinateImage (R : Set (Fin n → Fin d)) (ρ : Fin k → Fin n) : Set (Fin k → Fin d) :=
  {x | ∃ y ∈ R, y ∘ ρ = x}
def projectTuple (ρ : Fin k → Fin n) (x : Tuple (Fin d) n) : Tuple (Fin d) k := Vector.ofFn (view x ∘ ρ)
theorem coordinateImage_preserves {m : Operation (Fin d)} {R : Set (Fin n → Fin d)}
    (hR : Preserves m R) (ρ : Fin k → Fin n) : Preserves m (coordinateImage R ρ) := by
  rintro x ⟨x', hx, rfl⟩ y ⟨y', hy, rfl⟩ z ⟨z', hz, rfl⟩
  exact ⟨map₃ m x' y' z', hR _ hx _ hy _ hz, rfl⟩
def coordinatePins (ρ : Fin k → Fin n) (target : Tuple (Fin d) k) (len : ℕ) : List (FiniteConstraint d n) :=
  ((List.finRange k).filter (fun j => j.val < len)).map fun j =>
    ⟨1, fun _ => ρ j, fun x => decide (x 0 = view target j)⟩
theorem satisfies_coordinatePins (ρ : Fin k → Fin n) (target : Tuple (Fin d) k) (len : ℕ) (x : Fin n → Fin d) :
    Satisfies (coordinatePins ρ target len) x ↔ PrefixEq len (x ∘ ρ) (view target) := by
  simp [Satisfies, coordinatePins, PrefixEq, Function.comp_def]
theorem coordinatePins_preserved {m : Operation (Fin d)} (hm : IsMaltsev m)
    (ρ : Fin k → Fin n) (target : Tuple (Fin d) k) (len : ℕ) : TablesPreserved m (coordinatePins ρ target len) := by
  intro c hc
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hc
  intro x hx y hy z hz
  have hx' : x 0 = view target j := of_decide_eq_true hx
  have hy' : y 0 = view target j := of_decide_eq_true hy
  have hz' : z 0 = view target j := of_decide_eq_true hz
  apply decide_eq_true
  simp only [map₃, hx', hy', hz', hm.1]
def coordinateExtension (m : Operation (Fin d)) (W : Code (Fin d) n)
    (ρ : Fin k → Fin n) (target : Tuple (Fin d) k) (len : ℕ) : Option (Tuple (Fin d) k) :=
  (constructFrom m W (coordinatePins ρ target len)).seed.map (projectTuple ρ)
theorem coordinateExtension_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (ρ : Fin k → Fin n) (target : Tuple (Fin d) k) (len : ℕ) {result : Tuple (Fin d) k}
    (he : coordinateExtension m W ρ target len = some result) :
    view result ∈ coordinateImage R ρ ∧ PrefixEq len (view result) (view target) := by
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp he
  have h := constructFrom_correct hm (coordinatePins ρ target len) (coordinatePins_preserved hm ρ target len) W R hR hW
  have hs := h.seed_sound x hx
  simp only [projectTuple, view_ofFn]
  exact ⟨⟨view x, hs.1, rfl⟩, (satisfies_coordinatePins ρ target len _).mp hs.2⟩
theorem coordinateExtension_isSome {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (ρ : Fin k → Fin n) (target : Tuple (Fin d) k) (len : ℕ) :
    (coordinateExtension m W ρ target len).isSome = true ↔ ∃ x ∈ coordinateImage R ρ, PrefixEq len x (view target) := by
  constructor
  · intro h
    cases he : coordinateExtension m W ρ target len with
    | none => simp [he] at h
    | some x => exact ⟨view x, coordinateExtension_spec hm hR hW ρ target len he⟩
  · rintro ⟨x, ⟨y, hy, rfl⟩, hp⟩
    have h := constructFrom_correct hm (coordinatePins ρ target len) (coordinatePins_preserved hm ρ target len) W R hR hW
    obtain ⟨z, hz⟩ := h.seed_complete ⟨y, hy, (satisfies_coordinatePins ρ target len y).mpr hp⟩
    simp only [StoredCode.toCode] at hz
    simp [coordinateExtension, hz]
def imageCandidates (W : Code (Fin d) n) (ρ : Fin k → Fin n) (i : Fin k) : List (Tuple (Fin d) k) :=
  ((List.ofFn ((W.lookup (ρ i)))).flatMap Option.toList).map (projectTuple ρ)
def imageAnchor (m : Operation (Fin d)) (W : Code (Fin d) n)
    (ρ : Fin k → Fin n) (i : Fin k) (a : Fin d) : Option (Tuple (Fin d) k) :=
  (imageCandidates W ρ i).find?
    (fun z => (coordinateExtension m W ρ (replaceCoordinate z i a) (i.val + 1)).isSome)
def imageCode (m : Operation (Fin d)) (W : Code (Fin d) n) (ρ : Fin k → Fin n) : Code (Fin d) k where
  seed := W.seed.map (projectTuple ρ)
  lookup i a := (imageAnchor m W ρ i a).bind
    (fun z => coordinateExtension m W ρ (replaceCoordinate z i a) (i.val + 1))
theorem imageAnchor_congr {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (ρ : Fin k → Fin n) {i : Fin k} {a b : Fin d} (hab : Fork (coordinateImage R ρ) i a b) :
    imageAnchor m W ρ i a = imageAnchor m W ρ i b := by
  apply congrArg (fun p => (imageCandidates W ρ i).find? p)
  funext z
  apply Bool.eq_iff_iff.mpr
  rw [coordinateExtension_isSome hm hR hW, coordinateExtension_isSome hm hR hW]
  simp only [prefix_replace_iff]
  constructor
  · rintro ⟨x, hx, hzx, hxa⟩
    obtain ⟨y, hy, hxy, hyb⟩ := fork_transport hm (coordinateImage_preserves hR ρ) hab hx hxa
    exact ⟨y, hy, hzx.trans hxy, hyb⟩
  · rintro ⟨x, hx, hzx, hxb⟩
    obtain ⟨y, hy, hxy, hya⟩ := fork_transport hm (coordinateImage_preserves hR ρ) (fork_symm hab) hx hxb
    exact ⟨y, hy, hzx.trans hxy, hya⟩
theorem imageCode_lookup_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (ρ : Fin k → Fin n) {i : Fin k} {a : Fin d} {result : Tuple (Fin d) k}
    (he : (imageCode m W ρ).lookup i a = some result) :
    ∃ z, imageAnchor m W ρ i a = some z ∧ view result ∈ coordinateImage R ρ ∧
      PrefixEq i.val (view z) (view result) ∧ view result i = a := by
  change (imageAnchor m W ρ i a).bind _ = some result at he
  cases hz : imageAnchor m W ρ i a with
  | none => simp [hz] at he
  | some z =>
    simp only [hz, Option.bind_some] at he
    obtain ⟨hr, hp⟩ := coordinateExtension_spec hm hR hW ρ _ _ he
    exact ⟨z, rfl, hr, (prefix_replace_iff z i a _).mp hp⟩
theorem imageCode_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (ρ : Fin k → Fin n) : Correct (imageCode m W ρ) (coordinateImage R ρ) := by
  constructor
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Option.map_eq_some_iff.mp hx
    exact ⟨view y, hW.seed_sound y hy, by simp [projectTuple]⟩
  · rintro ⟨x, y, hy, _⟩
    obtain ⟨z, hz⟩ := hW.seed_complete ⟨y, hy⟩
    exact ⟨projectTuple ρ z, by simp [imageCode, hz]⟩
  · intro i a x hx
    obtain ⟨_, _, hxR, _, hxa⟩ := imageCode_lookup_spec hm hR hW ρ hx
    exact ⟨hxR, hxa⟩
  · rintro i x ⟨y, hy, rfl⟩
    obtain ⟨z, hz⟩ := hW.lookup_complete (ρ i) y hy
    have hzs := hW.lookup_sound _ _ _ hz
    have hzmem : projectTuple ρ z ∈ imageCandidates W ρ i := by
      simp only [imageCandidates, List.mem_map, List.mem_flatMap, List.mem_ofFn]
      exact ⟨z, ⟨_, ⟨y (ρ i), rfl⟩, by simpa using hz⟩, rfl⟩
    have hze : (coordinateExtension m W ρ
        (replaceCoordinate (projectTuple ρ z) i (y (ρ i))) (i.val + 1)).isSome = true := by
      apply (coordinateExtension_isSome hm hR hW ρ _ _).mpr
      refine ⟨view z ∘ ρ, ⟨view z, hzs.1, rfl⟩, ?_⟩
      apply (prefix_replace_iff _ _ _ _).mpr
      exact ⟨by simpa [projectTuple] using PrefixEq.refl i.val (view z ∘ ρ), hzs.2⟩
    have ha : (imageAnchor m W ρ i (y (ρ i))).isSome = true :=
      List.find?_isSome.mpr ⟨projectTuple ρ z, hzmem, hze⟩
    cases hu : imageAnchor m W ρ i (y (ρ i)) with
    | none => simp [hu] at ha
    | some u =>
      have ht := List.find?_some (show (imageCandidates W ρ i).find? _ = some u from hu)
      cases hr : coordinateExtension m W ρ (replaceCoordinate u i (y (ρ i))) (i.val + 1) with
      | none => simp [hr] at ht
      | some result => exact ⟨result, by simp [imageCode, hu, hr]⟩
  · intro i a b x y hab hx hy
    obtain ⟨u, hu, _, hux, _⟩ := imageCode_lookup_spec hm hR hW ρ hx
    obtain ⟨v, hv, _, hvy, _⟩ := imageCode_lookup_spec hm hR hW ρ hy
    have huv : u = v := Option.some.inj (hu.symm.trans ((imageAnchor_congr hm hR hW ρ hab).trans hv))
    subst v
    exact hux.symm.trans hvy
end ComplexCSP.MaltsevWitness
