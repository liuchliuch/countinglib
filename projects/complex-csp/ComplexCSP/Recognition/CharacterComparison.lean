import ComplexCSP.Instances.IsomorphismCompleteness
import ComplexCSP.Instances.PinnedMonoid
import ComplexCSP.Recognition.DegreeGenerated
import ComplexCSP.Algebra.ScalarTagsTyped

/-! # Exact comparison of tensor monomial characters

The finite checker uses all-instance isomorphism and preserves indexed symbols,
including collisions between tensorized tables. The scalar-tagged companion
verifies the paper's duplicate-free representation. -/

set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP.Recognition

open scoped BigOperators

section Retargeting

variable {A B C K ι V H : Type} {L : Language A K ι}

/-- Reinterpreting through an intermediate table family retains the exact same
symbol/scope list as direct reinterpretation. -/
theorem retarget_comp (I : Instance L V H)
    (g : (i : ι) → (Fin (L.arity i) → B) → K)
    (h : (i : ι) → (Fin (L.arity i) → C) → K) :
    (I.retarget g).retarget h = I.retarget h := by
  cases I
  simp only [Instance.retarget, List.map_map]
  rfl

/-- Interpreting the same tables is the identity on literal finite instances. -/
theorem retarget_self (I : Instance L V H) : I.retarget L.value = I := by
  cases I with
  | mk cs =>
    change Instance.mk (cs.map id) = Instance.mk cs
    rw [List.map_id]

end Retargeting

/-- A literal monomial is an ordered list of direct or conjugate coordinate
factors. Repeated factors and the empty monomial are represented explicitly. -/
abbrev PinnedMonomial (V D : Type) := List (PinnedCoordinate V D)

namespace PinnedMonomial

section Construction

variable {D K ι V : Type} [CommSemiring K] [StarRing K]

/-- The actual tensor domain has one coordinate for every listed factor. -/
abbrev Domain (M : PinnedMonomial V D) := Fin M.length → D

/-- Identity or conjugation on each finite tensor layer. -/
def layerMaps (M : PinnedMonomial V D) : Fin M.length → K →+* K :=
  fun j => Sum.elim (fun _ => RingHom.id K) (fun _ => starRingEnd K) (M.get j)

/-- Tensor the actual indexed language, retaining every symbol even when two
resulting tables happen to coincide. -/
def target (M : PinnedMonomial V D) (L : Language D K ι) : Language M.Domain K ι :=
  L.tensor M.layerMaps

/-- Transpose coordinate factors into the tensor-domain pin at each label. -/
def pin (M : PinnedMonomial V D) : V → M.Domain :=
  fun v j => Sum.elim (fun a => a v) (fun a => a v) (M.get j)

variable [Fintype D]

/-- The genuine monoid character of the listed coordinate factors. -/
def character (M : PinnedMonomial V D) (L : Language D K ι) : GeneratedTable L V →* K :=
  ∏ j, pinnedCoordinateCharacter L (M.get j)

@[simp] theorem character_apply (M : PinnedMonomial V D) (L : Language D K ι)
    (G : GeneratedTable L V) :
    M.character L G = ∏ j, Sum.elim G.val (fun a => star (G.val a)) (M.get j) := by
  simp only [character, MonoidHom.finset_prod_apply, pinnedCoordinateCharacter_apply]

/-- The computed tensor instance really realizes this monomial character. -/
theorem tensor_realizes {H : Type} [Fintype H] [DecidableEq H]
    (M : PinnedMonomial V D) (L : Language D K ι) (I : Instance L V H) :
    (I.retarget (M.target L).value).partition M.pin =
      M.character L ⟨I.partition, Instance.generated_partition I⟩ := by
  change (I.tensor M.layerMaps).partition M.pin = _
  rw [Instance.partition_tensor, character_apply]
  apply Finset.prod_congr rfl
  intro j hj
  cases hfactor : M.get j with
  | inl a => simp only [layerMaps, pin, hfactor, Sum.elim_inl, RingHom.id_apply]
  | inr a => simp only [layerMaps, pin, hfactor, Sum.elim_inr, starRingEnd_apply]


end Construction

section Comparison

variable {D K ι V : Type} [Field K] [StarRing K] [CharZero K]
variable [Fintype D] [DecidableEq D] [Fintype ι] [Fintype V] [DecidableEq K]

omit [CharZero K] [DecidableEq D] [Fintype ι] [Fintype V] [DecidableEq K] in
/-- Equality of actual monomial characters is precisely equality of the two
tensorized targets on all finite instance templates. -/
theorem characters_eq_iff_all_tensor_instances
    (M N : PinnedMonomial V D) (L : Language D K ι) :
    M.character L = N.character L ↔
      PinnedIsomorphism.AllPinnedEqual (M.target L) (N.target L).value M.pin N.pin := by
  constructor
  · intro hc H hH dH J
    let I : Instance L V H := J.retarget L.value
    have he := congrArg (fun χ : GeneratedTable L V →* K =>
      χ ⟨I.partition, Instance.generated_partition I⟩) hc
    change M.character L ⟨I.partition, Instance.generated_partition I⟩ =
      N.character L ⟨I.partition, Instance.generated_partition I⟩ at he
    rw [← tensor_realizes M L I, ← tensor_realizes N L I] at he
    dsimp only [I] at he
    rw [retarget_comp, retarget_comp] at he
    have hid : J.retarget (M.target L).value = J := retarget_self J
    rw [hid] at he
    exact he
  · intro h
    ext G
    obtain ⟨P, rfl⟩ := GeneratedTable.exists_presentation G
    have he := h (Fin P.hidden) (P.inst.retarget (M.target L).value)
    rw [retarget_comp] at he
    rw [tensor_realizes, tensor_realizes] at he
    exact he


/-- A total finite comparison algorithm: construct the two actual tensor tables
and enumerate their finite domain isomorphisms and pin-twin conditions. -/
def compare (L : Language D K ι) (M N : PinnedMonomial V D) : Bool :=
  (M.target L).pinnedIsoCheck (N.target L).value M.pin N.pin

/-- No equality matrix is assumed: the computed comparison is equivalent to
equality of the two genuine monoid characters. -/
theorem compare_correct (L : Language D K ι) (M N : PinnedMonomial V D) :
    compare L M N = true ↔ M.character L = N.character L := by
  rw [compare, PinnedIsomorphism.pinnedIsoCheck_correct_all_instances]
  exact (characters_eq_iff_all_tensor_instances M N L).symm

end Comparison

end PinnedMonomial

section CommonScalarTags

variable {A B K ι V H : Type} [Field K]
variable (L : Language A K ι)

/-- Common symbol scaling, exactly the preprocessing used for scalar tags. -/
def scaleSymbols (scalars : ι → K) : Language A K ι where
  arity := L.arity
  arity_pos := L.arity_pos
  value i a := scalars i * L.value i a

/-- The common nonzero factor contributed by the actual constraint occurrence
list. Repeated constraints contribute repeated tag factors. -/
def instanceTagProduct (scalars : ι → K) (I : Instance L V H) : K :=
  (I.constraints.map (fun c => scalars c.symbol)).prod

/-- Common symbol tags factor out of the actual pinned partition sum. -/
theorem partition_scaleSymbols [Fintype A] [Fintype H] [DecidableEq H]
    (scalars : ι → K) (I : Instance L V H) (a : V → A) :
    (I.retarget (scaleSymbols L scalars).value).partition a =
      instanceTagProduct L scalars I * I.partition a := by
  have he (b : H → A) : (I.retarget (scaleSymbols L scalars).value).eval a b =
      instanceTagProduct L scalars I * I.eval a b := by
    simp only [Instance.eval, Instance.retarget, List.map_map, Constraint.eval,
      scaleSymbols, Function.comp_def, instanceTagProduct]
    exact List.prod_map_mul
  simp only [Instance.partition, he, Finset.mul_sum]

/-- The tag product depends only on common symbols, not target interpretation. -/
theorem instanceTagProduct_retarget (scalars : ι → K) (I : Instance L V H)
    (g : (i : ι) → (Fin (L.arity i) → B) → K) :
    instanceTagProduct (L.retarget g) scalars (I.retarget g) = instanceTagProduct L scalars I := by
  simp only [instanceTagProduct, Instance.retarget, List.map_map]
  rfl

/-- Every factor remains nonzero, so the common occurrence product can be cancelled. -/
theorem instanceTagProduct_ne_zero (scalars : ι → K) (hscalars : ∀ i, scalars i ≠ 0)
    (I : Instance L V H) : instanceTagProduct L scalars I ≠ 0 := by
  apply List.prod_ne_zero
  intro hx
  obtain ⟨c, hc, he⟩ := List.mem_map.mp hx
  exact hscalars c.symbol he

/-- Actual finite-instance equality is unchanged by applying the same nonzero
symbol tags to both target families. -/
theorem partition_common_tags_iff [Fintype A] [Fintype B] [Fintype H] [DecidableEq H]
    (g : (i : ι) → (Fin (L.arity i) → B) → K)
    (scalars : ι → K) (hscalars : ∀ i, scalars i ≠ 0) (I : Instance L V H)
    (a : V → A) (b : V → B) :
    (I.retarget (scaleSymbols L scalars).value).partition a =
      (I.retarget (scaleSymbols (L.retarget g) scalars).value).partition b ↔
        I.partition a = (I.retarget g).partition b := by
  rw [partition_scaleSymbols]
  have ht := partition_scaleSymbols (L.retarget g) scalars (I.retarget g) b
  rw [retarget_comp, instanceTagProduct_retarget] at ht
  rw [ht]
  exact mul_left_cancel₀ (instanceTagProduct_ne_zero L scalars hscalars I) |> fun hh =>
    ⟨hh, congrArg (instanceTagProduct L scalars I * ·)⟩

/-- The full all-instance comparison is invariant under common nonzero symbol tags. -/
theorem allPinnedEqual_common_tags_iff [Fintype A] [Fintype B]
    (g : (i : ι) → (Fin (L.arity i) → B) → K)
    (scalars : ι → K) (hscalars : ∀ i, scalars i ≠ 0) (a : V → A) (b : V → B) :
    PinnedIsomorphism.AllPinnedEqual (scaleSymbols L scalars)
        (scaleSymbols (L.retarget g) scalars).value a b ↔
      PinnedIsomorphism.AllPinnedEqual L g a b := by
  constructor
  · intro h H hH dH I
    have he := h H (I.retarget (scaleSymbols L scalars).value)
    rw [retarget_comp] at he
    exact (partition_common_tags_iff L g scalars hscalars I a b).mp he
  · intro h H hH dH J
    let I : Instance L V H := J.retarget L.value
    have he := (partition_common_tags_iff L g scalars hscalars I a b).mpr (h H I)
    dsimp only [I] at he
    rw [retarget_comp, retarget_comp] at he
    have hid : J.retarget (scaleSymbols L scalars).value = J := retarget_self J
    rwa [hid] at he

end CommonScalarTags

namespace PinnedMonomial

variable {D K ι V : Type} [Field K] [StarRing K] [CharZero K]
variable [Fintype D] [DecidableEq D] [Fintype ι] [Fintype V] [DecidableEq K]

/-- Optional paper-style common positive integer tags. A tag vector supplied by
`ScalarTags.findTagCode` may be used here; correctness needs only positivity,
while its separate specification additionally supplies table distinctness. -/
def compareWithPositiveTags (L : Language D K ι) (tag : ι → ℕ)
    (M N : PinnedMonomial V D) : Bool :=
  (scaleSymbols (M.target L) (fun i => ((tag i + 1 : ℕ) : K))).pinnedIsoCheck
    (scaleSymbols (N.target L) (fun i => ((tag i + 1 : ℕ) : K))).value M.pin N.pin

/-- Paper-style positive tagging and the untagged indexed-family algorithm decide
exactly the same genuine monomial-character equality. -/
theorem compareWithPositiveTags_correct (L : Language D K ι) (tag : ι → ℕ)
    (M N : PinnedMonomial V D) :
    compareWithPositiveTags L tag M N = true ↔ M.character L = N.character L := by
  rw [compareWithPositiveTags, PinnedIsomorphism.pinnedIsoCheck_correct_all_instances]
  exact (allPinnedEqual_common_tags_iff (M.target L) (N.target L).value
    (fun i => ((tag i + 1 : ℕ) : K)) (fun i => Nat.cast_ne_zero.mpr (Nat.succ_ne_zero _))
    M.pin N.pin).trans (characters_eq_iff_all_tensor_instances M N L).symm

end PinnedMonomial

section JointComparisons

open PinnedIsomorphism

variable {A B K ι V : Type} [Field K] [CharZero K]
variable [Fintype A] [Fintype B]
variable (L : Language A K ι)
variable (g : (i : ι) → (Fin (L.arity i) → B) → K)

omit [CharZero K] in
/-- Two source-side characters agree exactly when the source pins agree on all
instances, even though their ambient monoid also remembers target evaluations. -/
theorem sourcePinCharacter_eq_iff (a a' : V → A) :
    sourcePinCharacter L g a = sourcePinCharacter L g a' ↔
      AllPinnedEqual L L.value a a' := by
  constructor
  · intro h H hH dH I
    have he := congrArg (fun χ => χ (jointElement L g I)) h
    change I.partition a = I.partition a' at he
    simpa only [retarget_self] using he
  · intro h
    ext p
    obtain ⟨n, I, he⟩ := p.property
    change p.val.1 a = p.val.1 a'
    rw [he]
    have hh := h (Fin n) I
    simp only [retarget_self] at hh
    exact hh

omit [CharZero K] in
/-- The analogous exact comparison of two target-side characters. -/
theorem targetPinCharacter_eq_iff (b b' : V → B) :
    targetPinCharacter L g b = targetPinCharacter L g b' ↔
      AllPinnedEqual (L.retarget g) g b b' := by
  constructor
  · intro h H hH dH J
    let I : Instance L V H := J.retarget L.value
    have he := congrArg (fun χ => χ (jointElement L g I)) h
    change (I.retarget g).partition b = (I.retarget g).partition b' at he
    have hr : I.retarget g = J := Instance.retarget_back J L.value
    rw [hr] at he
    have hj : J.retarget g = J := retarget_self J
    simpa only [hj] using he
  · intro h
    ext p
    obtain ⟨n, I, he⟩ := p.property
    change p.val.2 b = p.val.2 b'
    rw [he]
    have hh := h (Fin n) (I.retarget g)
    have hr : (I.retarget g).retarget g = I.retarget g := retarget_self (I.retarget g)
    simp only [hr] at hh
    exact hh

/-- A pin character on either side of the actual shared-instance monoid. -/
def jointPinCharacter : (V → A) ⊕ (V → B) → jointMonoid (V := V) L g →* K :=
  Sum.elim (sourcePinCharacter L g) (targetPinCharacter L g)

variable [DecidableEq A] [DecidableEq B] [DecidableEq K] [Fintype ι] [Fintype V]

/-- Compare source/source, source/target, or target/target pins by actual finite
isomorphism checks. The reverse cross case uses symmetry of equality. -/
def compareJointPins : ((V → A) ⊕ (V → B)) → ((V → A) ⊕ (V → B)) → Bool
  | .inl a, .inl a' => L.pinnedIsoCheck L.value a a'
  | .inl a, .inr b => L.pinnedIsoCheck g a b
  | .inr b, .inl a => L.pinnedIsoCheck g a b
  | .inr b, .inr b' => (L.retarget g).pinnedIsoCheck g b b'

theorem compareJointPins_correct (u v : (V → A) ⊕ (V → B)) :
    compareJointPins L g u v = true ↔ jointPinCharacter L g u = jointPinCharacter L g v := by
  cases u with
  | inl a =>
    cases v with
    | inl a' =>
      exact (pinnedIsoCheck_correct_all_instances L L.value a a').trans
        (sourcePinCharacter_eq_iff L g a a').symm
    | inr b =>
      exact (pinnedIsoCheck_correct_all_instances L g a b).trans (pinCharacter_eq_iff L g a b).symm
  | inr b =>
    cases v with
    | inl a =>
      exact ((pinnedIsoCheck_correct_all_instances L g a b).trans
        (pinCharacter_eq_iff L g a b).symm).trans eq_comm
    | inr b' =>
      exact (pinnedIsoCheck_correct_all_instances (L.retarget g) g b b').trans
        (targetPinCharacter_eq_iff L g b b').symm

variable {S T : Type} [Fintype S] [Fintype T]

/-- Compute whether the sum of finitely many source-pinned characters equals
the sum of finitely many target-pinned characters. -/
def pinSumTest (a : S → V → A) (b : T → V → B) : Bool :=
  indexedCharacterZeroTest (Finset.univ : Finset (S ⊕ T))
    (fun i j => compareJointPins L g
      (Sum.elim (fun s => Sum.inl (a s)) (fun t => Sum.inr (b t)) i)
      (Sum.elim (fun s => Sum.inl (a s)) (fun t => Sum.inr (b t)) j))
    (Sum.elim (fun _ => (1 : K)) (fun _ => -1))

/-- Exactness of the finite computed matrix for these two character sums. -/
theorem pinSumTest_correct (a : S → V → A) (b : T → V → B) :
    pinSumTest L g a b = true ↔
      ∀ (H : Type) [Fintype H] [DecidableEq H], ∀ I : Instance L V H,
        (∑ s, I.partition (a s)) = ∑ t, (I.retarget g).partition (b t) := by
  let pin : S ⊕ T → (V → A) ⊕ (V → B) :=
    Sum.elim (fun s => Sum.inl (a s)) (fun t => Sum.inr (b t))
  let χ : S ⊕ T → jointMonoid (V := V) L g →* K := fun i => jointPinCharacter L g (pin i)
  have ht := indexedCharacterZeroTest_correct (Finset.univ : Finset (S ⊕ T)) χ
    (fun i j => compareJointPins L g (pin i) (pin j))
    (Sum.elim (fun _ => (1 : K)) (fun _ => -1))
    (fun i _ j _ => compareJointPins_correct L g (pin i) (pin j))
  change pinSumTest L g a b = true ↔ _ at ht
  rw [ht]
  have hsum (p : jointMonoid (V := V) L g) :
      (∑ i : S ⊕ T, Sum.elim (fun _ => (1 : K)) (fun _ => -1) i * χ i p) = 0 ↔
        (∑ s, p.val.1 (a s)) = ∑ t, p.val.2 (b t) := by
    simp only [Fintype.sum_sum_type, χ, pin, jointPinCharacter,
      sourcePinCharacter, targetPinCharacter, Sum.elim_inl, Sum.elim_inr,
      one_mul, neg_one_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero,
      MonoidHom.coe_mk, OneHom.coe_mk]
  simp_rw [hsum]
  constructor
  · intro h H hH dH I
    exact h (jointElement L g I)
  · intro h p
    obtain ⟨n, I, he⟩ := p.property
    rw [he]
    exact h (Fin n) I

end JointComparisons

section RetargetDegrees

variable {A B K ι V H : Type} {L : Language A K ι}

/-- Retargeting leaves the exact occurrence list unchanged. -/
theorem occurrences_retarget (I : Instance L V H)
    (g : (i : ι) → (Fin (L.arity i) → B) → K) :
    (I.retarget g).occurrences = I.occurrences := by
  cases I with
  | mk cs =>
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simpa only [Instance.occurrences, Instance.retarget, List.map_cons,
        List.flatMap_cons] using congrArg (List.ofFn c.scope ++ ·) ih

theorem occurrenceDegree_retarget [DecidableEq V] [DecidableEq H]
    (I : Instance L V H) (g : (i : ι) → (Fin (L.arity i) → B) → K) (v : V ⊕ H) :
    (I.retarget g).occurrenceDegree v = I.occurrenceDegree v := by
  simp only [Instance.occurrenceDegree, occurrences_retarget]

/-- The cyclic table augmentation is literal retargeting of the same scopes. -/
theorem degreeAugment_eq_retarget [CommSemiring K]
    (I : Instance L V H) (δ : ℕ) (ζ : K) :
    I.degreeAugment δ ζ = I.retarget (L.degreeAugment δ ζ).value := rfl

/-- Any finite hidden-variable type can be encoded canonically without losing
its degree certificate or its exact partition table. -/
theorem degreeGenerated_partition [CommSemiring K] [Fintype A]
    [Fintype H] [DecidableEq H] [DecidableEq V]
    {δ : ℕ} (I : Instance L V H) (hI : I.DegreeDivisible δ) :
    DegreeGenerated L δ I.partition := by
  classical
  refine ⟨⟨Fintype.card H, I.renameHidden (Fintype.equivFin H)⟩, ?_, ?_⟩
  · exact (Instance.degreeDivisible_renameHidden_equiv_iff I (Fintype.equivFin H) δ).mpr hI
  · funext a
    exact Instance.partition_renameHidden_equiv I (Fintype.equivFin H) a

end RetargetDegrees

namespace PinnedMonomial

section DegreeFilterComparison

variable {D K ι V : Type} [Field K] [StarRing K] [CharZero K]
variable [Fintype D] [DecidableEq D] [Fintype ι]
variable [Fintype V] [DecidableEq V] [DecidableEq K]

/-- The actual monomial tensor target with one auxiliary cyclic coordinate. -/
def filteredTarget (M : PinnedMonomial V D) (L : Language D K ι) (δ : ℕ) (ζ : K) :=
  (M.target L).degreeAugment δ ζ

/-- Enumerate every assignment of cyclic values to the original boundary labels. -/
def filteredPin (M : PinnedMonomial V D) {δ : ℕ} (s : V → Fin δ) :
    V → M.Domain × Fin δ := fun v => (M.pin v, s v)

omit [CharZero K] [DecidableEq D] [Fintype ι] [DecidableEq K] in
/-- The exact paper filter identity for this actual tensor monomial, expressed
using the original instance's occurrence degrees and genuine monoid character. -/
theorem filtered_sum_formula {H : Type} [Fintype H] [DecidableEq H]
    (M : PinnedMonomial V D) (L : Language D K ι) {δ : ℕ} {ζ : K}
    (hζ : IsPrimitiveRoot ζ δ) (I : Instance L V H) :
    (∑ s : V → Fin δ,
      (I.retarget (M.filteredTarget L δ ζ).value).partition (M.filteredPin s)) =
      if I.DegreeDivisible δ then
        (δ : K) ^ (Fintype.card V + Fintype.card H) *
          M.character L ⟨I.partition, Instance.generated_partition I⟩ else 0 := by
  have hf := Instance.degree_filter_identity (I.retarget (M.target L).value) hζ M.pin
  simp only [degreeAugment_eq_retarget, retarget_comp, occurrenceDegree_retarget] at hf
  rw [tensor_realizes M L I] at hf
  exact hf

/-- Execute the finite sum-of-filtered-characters comparison. Every equality
in its matrix is obtained from a finite target-isomorphism enumeration. -/
def degreeCompare (L : Language D K ι) (δ : ℕ) (ζ : K)
    (M N : PinnedMonomial V D) : Bool :=
  pinSumTest (M.filteredTarget L δ ζ) (N.filteredTarget L δ ζ).value
    (M.filteredPin (δ := δ)) (N.filteredPin (δ := δ))

/-- The computed filter comparison is equivalent to equality of the averaged
augmented pinned values on every actual original instance template. -/
theorem degreeCompare_sum_correct (L : Language D K ι) (δ : ℕ) (ζ : K)
    (M N : PinnedMonomial V D) :
    degreeCompare L δ ζ M N = true ↔
      ∀ (H : Type) [Fintype H] [DecidableEq H], ∀ I : Instance L V H,
        (∑ s : V → Fin δ,
          (I.retarget (M.filteredTarget L δ ζ).value).partition (M.filteredPin s)) =
        ∑ s : V → Fin δ,
          (I.retarget (N.filteredTarget L δ ζ).value).partition (N.filteredPin s) := by
  rw [degreeCompare, pinSumTest_correct]
  constructor
  · intro h H hH dH I
    have he := h H (I.retarget (M.filteredTarget L δ ζ).value)
    simpa only [retarget_comp] using he
  · intro h H hH dH J
    have he := h H (J.retarget L.value)
    simp only [retarget_comp] at he
    have hid : J.retarget (M.filteredTarget L δ ζ).value = J := retarget_self J
    simpa only [hid] using he

/-- The genuine restriction of a monomial character to degree-generated tables. -/
def degreeCharacter (M : PinnedMonomial V D) (L : Language D K ι) (δ : ℕ) :
    DegreeGeneratedTable (B := V) L δ →* K :=
  (M.character L).comp DegreeGeneratedTable.inclusion

/-- The full cyclic-filter reduction is proved, including cancellation of the
nonzero δ-power and actual degree-divisible witnesses. The primitive root and
its field are explicit certified inputs, not supplied by an unproved construction. -/
theorem degreeCompare_correct (L : Language D K ι) {δ : ℕ} {ζ : K}
    (hδ : 0 < δ) (hζ : IsPrimitiveRoot ζ δ) (M N : PinnedMonomial V D) :
    degreeCompare L δ ζ M N = true ↔ M.degreeCharacter L δ = N.degreeCharacter L δ := by
  rw [degreeCompare_sum_correct]
  constructor
  · intro h
    ext G
    obtain ⟨P, hP, rfl⟩ := DegreeGeneratedTable.exists_presentation G
    have he := h (Fin P.hidden) P.inst
    rw [filtered_sum_formula M L hζ, filtered_sum_formula N L hζ] at he
    have hp : P.inst.DegreeDivisible δ := hP
    rw [if_pos hp, if_pos hp] at he
    have hn : (δ : K) ^ (Fintype.card V + Fintype.card (Fin P.hidden)) ≠ 0 :=
      pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hδ))
    exact mul_left_cancel₀ hn he
  · intro hc H hH dH I
    rw [filtered_sum_formula M L hζ, filtered_sum_formula N L hζ]
    by_cases hI : I.DegreeDivisible δ
    · rw [if_pos hI, if_pos hI]
      congr 1
      exact congrArg (fun χ : DegreeGeneratedTable (B := V) L δ →* K =>
        χ ⟨I.partition, degreeGenerated_partition I hI⟩) hc
    · rw [if_neg hI, if_neg hI]

end DegreeFilterComparison

end PinnedMonomial

namespace PinnedMonomial

section PaperTagSearch

variable {D K V : Type} {k : ℕ} [Field K] [StarRing K] [CharZero K]
variable [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq K]

/-- Run the proved typed common-tag search on the two actual tensor families.
The hypotheses are precisely the per-arity zero-table condition needed by that
search, and are unrelated to the desired character-equality answer. -/
def paperTagVector (L : Language D K (Fin k)) (M N : PinnedMonomial V D)
    (hM : ∀ i j, i ≠ j → L.arity i = L.arity j →
      (M.target L).value i ≠ 0 ∨ (M.target L).value j ≠ 0)
    (hN : ∀ i j, i ≠ j → L.arity i = L.arity j →
      (N.target L).value i ≠ 0 ∨ (N.target L).value j ≠ 0) : Fin k → ℕ :=
  ScalarTags.tagCandidate k (ScalarTags.findTagCode (K := K)
    (E := fun r => (Fin r → M.Domain) → K) (F := fun r => (Fin r → N.Domain) → K) L.arity
    (M.target L).value (N.target L).value hM hN)

omit [DecidableEq D] [Fintype V] in
/-- The computed common tags really make both varying-arity families duplicate-free. -/
theorem paperTagVector_separates (L : Language D K (Fin k)) (M N : PinnedMonomial V D)
    (hM : ∀ i j, i ≠ j → L.arity i = L.arity j →
      (M.target L).value i ≠ 0 ∨ (M.target L).value j ≠ 0)
    (hN : ∀ i j, i ≠ j → L.arity i = L.arity j →
      (N.target L).value i ≠ 0 ∨ (N.target L).value j ≠ 0) :
    let tags := paperTagVector L M N hM hN
    Function.Injective (fun i =>
      (⟨L.arity i, ((tags i + 1 : ℕ) : K) • (M.target L).value i⟩ :
        (r : ℕ) × ((Fin r → M.Domain) → K))) ∧
    Function.Injective (fun i =>
      (⟨L.arity i, ((tags i + 1 : ℕ) : K) • (N.target L).value i⟩ :
        (r : ℕ) × ((Fin r → N.Domain) → K))) := by
  have hs := ScalarTags.findTagCode_spec (K := K)
    (E := fun r => (Fin r → M.Domain) → K) (F := fun r => (Fin r → N.Domain) → K) L.arity
    (M.target L).value (N.target L).value hM hN
  simp only [ScalarTags.tagsAccept, decide_eq_true_eq] at hs
  exact ⟨fun {_ _} h ↦ hs.1 _ _ h, fun {_ _} h ↦ hs.2 _ _ h⟩

/-- A fully computed paper-style tagged comparison, rather than a supplied tag vector. -/
def comparePaperTagged (L : Language D K (Fin k)) (M N : PinnedMonomial V D)
    (hM : ∀ i j, i ≠ j → L.arity i = L.arity j →
      (M.target L).value i ≠ 0 ∨ (M.target L).value j ≠ 0)
    (hN : ∀ i j, i ≠ j → L.arity i = L.arity j →
      (N.target L).value i ≠ 0 ∨ (N.target L).value j ≠ 0) : Bool :=
  compareWithPositiveTags L (paperTagVector L M N hM hN) M N

/-- Correctness of the actual tag-search/table-enumeration flow follows by the
proved occurrence-wise common-factor cancellation, including repeated constraints. -/
theorem comparePaperTagged_correct (L : Language D K (Fin k)) (M N : PinnedMonomial V D)
    (hM : ∀ i j, i ≠ j → L.arity i = L.arity j →
      (M.target L).value i ≠ 0 ∨ (M.target L).value j ≠ 0)
    (hN : ∀ i j, i ≠ j → L.arity i = L.arity j →
      (N.target L).value i ≠ 0 ∨ (N.target L).value j ≠ 0) :
    comparePaperTagged L M N hM hN = true ↔ M.character L = N.character L :=
  compareWithPositiveTags_correct L (paperTagVector L M N hM hN) M N

end PaperTagSearch

end PinnedMonomial

end ComplexCSP.Recognition
