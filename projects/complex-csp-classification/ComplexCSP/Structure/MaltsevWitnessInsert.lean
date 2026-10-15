import ComplexCSP.Structure.MaltsevWitnessConstraint
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n r : ℕ}
def constraintRelation (R : Set (Fin n → Fin d)) (scope : Fin r → Fin n)
    (accept : (Fin r → Fin d) → Bool) : Set (Fin n → Fin d) := {x | x ∈ R ∧ accept (x ∘ scope) = true}
theorem constraintRelation_preserves {m : Operation (Fin d)} {R : Set (Fin n → Fin d)}
    (hR : Preserves m R) (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool)
    (hC : Preserves m {x | accept x = true}) : Preserves m (constraintRelation R scope accept) := by
  intro x hx y hy z hz
  exact ⟨hR _ hx.1 _ hy.1 _ hz.1, hC _ hx.2 _ hy.2 _ hz.2⟩
def constraintSeeds (m : Operation (Fin d)) (W : Code (Fin d) n)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) : List (Tuple (Fin d) n) :=
  (projectedClosure m scope (storedRows W)).filter (fun x => accept (projectionKey scope x))
theorem constraintSeeds_sound {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) {x : Tuple (Fin d) n}
    (hx : x ∈ constraintSeeds m W scope accept) : view x ∈ constraintRelation R scope accept := by
  obtain ⟨hx, ha⟩ := List.mem_filter.mp hx
  exact ⟨(projectedClosure_witnesses hm hR hW scope).1 _ hx, ha⟩
theorem constraintSeeds_complete {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) {x : Fin n → Fin d}
    (hx : x ∈ constraintRelation R scope accept) : ∃ y, y ∈ constraintSeeds m W scope accept := by
  obtain ⟨y, hy, he⟩ := (projectedClosure_witnesses hm hR hW scope).2 x hx.1
  exact ⟨y, List.mem_filter.mpr ⟨hy, by simpa [he] using hx.2⟩⟩
def constraintCandidates (m : Operation (Fin d)) (W : Code (Fin d) n)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (i : Fin n) : List (Tuple (Fin d) n) :=
  (projectedClosure m (Fin.cons i scope) (storedRows W)).filter (fun x => accept (projectionKey scope x))
theorem constraintCandidates_sound {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (i : Fin n) {x : Tuple (Fin d) n}
    (hx : x ∈ constraintCandidates m W scope accept i) : view x ∈ constraintRelation R scope accept := by
  obtain ⟨hx, ha⟩ := List.mem_filter.mp hx
  exact ⟨(projectedClosure_witnesses hm hR hW (Fin.cons i scope)).1 _ hx, ha⟩
theorem constraintCandidates_complete {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (i : Fin n) {x : Fin n → Fin d}
    (hx : x ∈ constraintRelation R scope accept) : ∃ y ∈ constraintCandidates m W scope accept i, view y i = x i := by
  obtain ⟨y, hy, he⟩ := (projectedClosure_witnesses hm hR hW (Fin.cons i scope)).2 x hx.1
  have he' : projectionKey scope y = x ∘ scope := by
    funext j
    exact congrFun he j.succ
  exact ⟨y, List.mem_filter.mpr ⟨hy, by simpa [he'] using hx.2⟩, congrFun he 0⟩
def constraintExtension (m : Operation (Fin d)) (W : Code (Fin d) n)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (i : Fin n) (a : Fin d)
    (z : Tuple (Fin d) n) : Option (Tuple (Fin d) n) :=
  (constrainedExtensions m W (replaceCoordinate z i a) (i.val + 1) scope accept).head?
theorem constraintExtension_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (i : Fin n) (a : Fin d)
    (z : Tuple (Fin d) n) {result : Tuple (Fin d) n}
    (he : constraintExtension m W scope accept i a z = some result) :
    view result ∈ constraintRelation R scope accept ∧ PrefixEq i.val (view z) (view result) ∧ view result i = a := by
  have hmem : result ∈ constrainedExtensions m W (replaceCoordinate z i a) (i.val + 1) scope accept := by
    change (constrainedExtensions m W (replaceCoordinate z i a) (i.val + 1) scope accept).head? = some result at he
    generalize hs : constrainedExtensions m W (replaceCoordinate z i a) (i.val + 1) scope accept = xs at *
    cases xs with
    | nil => contradiction
    | cons x xs =>
      have hx : x = result := Option.some.inj he
      subst x
      exact List.mem_cons_self
  obtain ⟨hr, hp, ha⟩ := constrainedExtensions_sound hm hR hW _ _ scope accept hmem
  exact ⟨⟨hr, ha⟩, (prefix_replace_iff z i a _).mp hp⟩
theorem constraintExtension_isSome {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (i : Fin n) (a : Fin d) (z : Tuple (Fin d) n) :
    (constraintExtension m W scope accept i a z).isSome = true ↔
      ∃ x ∈ constraintRelation R scope accept, PrefixEq i.val (view z) x ∧ x i = a := by
  constructor
  · intro h
    cases he : constraintExtension m W scope accept i a z with
    | none => simp [he] at h
    | some result => exact ⟨view result, constraintExtension_spec hm hR hW scope accept i a z he⟩
  · rintro ⟨x, ⟨hx, ha⟩, hp⟩
    obtain ⟨y, hy, _⟩ := constrainedExtensions_complete hm hR hW _ _ scope accept hx
      ((prefix_replace_iff z i a x).mpr hp) ha
    unfold constraintExtension
    generalize hs : constrainedExtensions m W (replaceCoordinate z i a) (i.val + 1) scope accept = xs at *
    cases xs with
    | nil => simp at hy
    | cons t ts => rfl
def constraintAnchor (m : Operation (Fin d)) (W : Code (Fin d) n)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (i : Fin n) (a : Fin d) : Option (Tuple (Fin d) n) :=
  (constraintCandidates m W scope accept i).find? (fun z => (constraintExtension m W scope accept i a z).isSome)
def insertConstraint (m : Operation (Fin d)) (W : Code (Fin d) n)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) : Code (Fin d) n where
  seed := (constraintSeeds m W scope accept).head?
  lookup i a := (constraintAnchor m W scope accept i a).bind (constraintExtension m W scope accept i a)
theorem constraintAnchor_congr {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (hC : Preserves m {x | accept x = true})
    {i : Fin n} {a b : Fin d} (hab : Fork (constraintRelation R scope accept) i a b) :
    constraintAnchor m W scope accept i a = constraintAnchor m W scope accept i b := by
  apply congrArg (fun p => (constraintCandidates m W scope accept i).find? p)
  funext z
  apply Bool.eq_iff_iff.mpr
  rw [constraintExtension_isSome hm hR hW, constraintExtension_isSome hm hR hW]
  have hU := constraintRelation_preserves hR scope accept hC
  constructor
  · rintro ⟨x, hx, hzx, hxa⟩
    obtain ⟨y, hy, hxy, hyb⟩ := fork_transport hm hU hab hx hxa
    exact ⟨y, hy, hzx.trans hxy, hyb⟩
  · rintro ⟨x, hx, hzx, hxb⟩
    obtain ⟨y, hy, hxy, hya⟩ := fork_transport hm hU (fork_symm hab) hx hxb
    exact ⟨y, hy, hzx.trans hxy, hya⟩
theorem insertConstraint_lookup_spec {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) {i : Fin n} {a : Fin d} {result : Tuple (Fin d) n}
    (he : (insertConstraint m W scope accept).lookup i a = some result) :
    ∃ z, constraintAnchor m W scope accept i a = some z ∧ view result ∈ constraintRelation R scope accept ∧
      PrefixEq i.val (view z) (view result) ∧ view result i = a := by
  change (constraintAnchor m W scope accept i a).bind _ = some result at he
  cases hz : constraintAnchor m W scope accept i a with
  | none => simp [hz] at he
  | some z =>
    simp only [hz, Option.bind_some] at he
    exact ⟨z, rfl, constraintExtension_spec hm hR hW scope accept i a z he⟩
theorem insertConstraint_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (scope : Fin r → Fin n) (accept : (Fin r → Fin d) → Bool) (hC : Preserves m {x | accept x = true}) :
    Correct (insertConstraint m W scope accept) (constraintRelation R scope accept) := by
  constructor
  · intro x hx
    have hmem : x ∈ constraintSeeds m W scope accept := by
      change (constraintSeeds m W scope accept).head? = some x at hx
      generalize hs : constraintSeeds m W scope accept = xs at *
      cases xs with
      | nil => contradiction
      | cons y ys =>
        have hy : y = x := Option.some.inj hx
        subst y
        exact List.mem_cons_self
    exact constraintSeeds_sound hm hR hW scope accept hmem
  · rintro ⟨x, hx⟩
    obtain ⟨y, hy⟩ := constraintSeeds_complete hm hR hW scope accept hx
    change ∃ y, (constraintSeeds m W scope accept).head? = some y
    generalize hs : constraintSeeds m W scope accept = xs at *
    cases xs with
    | nil => simp at hy
    | cons z zs => exact ⟨z, rfl⟩
  · intro i a x hx
    obtain ⟨_, _, hxR, _, hxa⟩ := insertConstraint_lookup_spec hm hR hW scope accept hx
    exact ⟨hxR, hxa⟩
  · intro i x hx
    obtain ⟨y, hy, hyi⟩ := constraintCandidates_complete hm hR hW scope accept i hx
    have hyR := constraintCandidates_sound hm hR hW scope accept i hy
    have he : (constraintExtension m W scope accept i (x i) y).isSome = true :=
      (constraintExtension_isSome hm hR hW scope accept i (x i) y).mpr ⟨view y, hyR, PrefixEq.refl _ _, hyi⟩
    have ha : (constraintAnchor m W scope accept i (x i)).isSome = true := List.find?_isSome.mpr ⟨y, hy, he⟩
    cases hz : constraintAnchor m W scope accept i (x i) with
    | none => simp [hz] at ha
    | some z =>
      have he' := List.find?_some (show (constraintCandidates m W scope accept i).find? _ = some z from hz)
      cases hr : constraintExtension m W scope accept i (x i) z with
      | none => simp [hr] at he'
      | some result => exact ⟨result, by simp [insertConstraint, hz, hr]⟩
  · intro i a b x y hab hx hy
    obtain ⟨u, hu, _, hux, _⟩ := insertConstraint_lookup_spec hm hR hW scope accept hx
    obtain ⟨v, hv, _, hvy, _⟩ := insertConstraint_lookup_spec hm hR hW scope accept hy
    have huv : u = v := Option.some.inj
      (hu.symm.trans ((constraintAnchor_congr hm hR hW scope accept hC hab).trans hv))
    subst v
    exact hux.symm.trans hvy
end ComplexCSP.MaltsevWitness
