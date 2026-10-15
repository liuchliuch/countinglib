import ComplexCSP.Instances.AllInstanceIsomorphism
import ComplexCSP.Instances.IsomorphismTwins
import Mathlib.SetTheory.Cardinal.Finite

/-! # Extension of indistinguishable pins

Exact finite-instance equality extends prescribed pins while retaining their
original positions. This is the extension step for all-instance isomorphism. -/
namespace ComplexCSP
namespace Instance
variable {A B K ι V V' H H' T : Type} {L : Language A K ι}

@[simp] theorem retarget_renameBoundary (I : Instance L V H)
    (g : (i : ι) → (Fin (L.arity i) → B) → K) (f : V → V') :
    (I.renameBoundary f).retarget g = (I.retarget g).renameBoundary f := by
  cases I
  simp only [retarget, renameBoundary, List.map_map]
  rfl

@[simp] theorem retarget_renameHidden (I : Instance L V H)
    (g : (i : ι) → (Fin (L.arity i) → B) → K) (f : H → H') :
    (I.renameHidden f).retarget g = (I.retarget g).renameHidden f := by
  cases I
  simp only [retarget, renameHidden, List.map_map]
  rfl

@[simp] theorem retarget_glue (I : Instance L V H) (J : Instance L V H')
    (g : (i : ι) → (Fin (L.arity i) → B) → K) :
    (I.glue J).retarget g = (I.retarget g).glue (J.retarget g) := by
  simp only [glue, retarget, renameHidden, List.map_append, List.map_map]
  rfl

@[simp] theorem retarget_hideBoundary (I : Instance L (V ⊕ T) H)
    (g : (i : ι) → (Fin (L.arity i) → B) → K) :
    I.hideBoundary.retarget g = (I.retarget g).hideBoundary := by
  cases I
  simp only [retarget, hideBoundary, List.map_map]
  rfl
end Instance

namespace PinnedIsomorphism
open scoped BigOperators
noncomputable section

variable {A B K ι V T : Type} [Field K] [CharZero K]
variable [Fintype A] [Fintype B]
variable (L : Language A K ι)
variable (g : (i : ι) → (Fin (L.arity i) → B) → K)

/-- The source/target pair evaluated on the same underlying instance template. -/
def pairedPartition {H : Type} [Fintype H] [DecidableEq H] (I : Instance L V H) :
    ((V → A) → K) × ((V → B) → K) :=
  (I.partition, (I.retarget g).partition)

omit [CharZero K] in
theorem pairedPartition_renameHidden {H H' : Type}
    [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
    (I : Instance L V H) (e : H ≃ H') :
    pairedPartition L g (I.renameHidden e) = pairedPartition L g I := by
  apply Prod.ext
  · funext a
    exact I.partition_renameHidden_equiv e a
  · funext b
    simp only [pairedPartition, Instance.retarget_renameHidden]
    exact (I.retarget g).partition_renameHidden_equiv e b

omit [CharZero K] in
theorem pairedPartition_glue {H H' : Type}
    [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H']
    (I : Instance L V H) (J : Instance L V H') :
    pairedPartition L g (I.glue J) = pairedPartition L g I * pairedPartition L g J := by
  apply Prod.ext
  · funext a
    exact I.partition_glue J a
  · funext b
    simp only [pairedPartition, Instance.retarget_glue]
    exact (I.retarget g).partition_glue (J.retarget g) b

/-- Every pair has a single finite witness, not two independently chosen tables. -/
def JointGenerated (p : ((V → A) → K) × ((V → B) → K)) : Prop :=
  ∃ n : ℕ, ∃ I : Instance L V (Fin n), p = pairedPartition L g I

/-- The commutative monoid of jointly generated source/target table pairs. -/
def jointMonoid : Submonoid (((V → A) → K) × ((V → B) → K)) where
  carrier := JointGenerated L g
  one_mem' := by
    refine ⟨0, ⟨[]⟩, ?_⟩
    apply Prod.ext <;> funext a <;>
      simp [pairedPartition, Instance.partition, Instance.eval, Instance.retarget]
  mul_mem' := by
    rintro p q ⟨n, I, rfl⟩ ⟨m, J, rfl⟩
    refine ⟨n + m, (I.glue J).renameHidden finSumFinEquiv, ?_⟩
    rw [pairedPartition_renameHidden, pairedPartition_glue]

/-- Canonicalize any finite hidden-variable type without changing either target. -/
def jointElement {H : Type} [Fintype H] [DecidableEq H] (I : Instance L V H) :
    jointMonoid (V := V) L g := by
  classical
  refine ⟨pairedPartition L g I, Fintype.card H,
    I.renameHidden (Fintype.equivFin H), ?_⟩
  exact (pairedPartition_renameHidden L g I (Fintype.equivFin H)).symm

/-- Evaluation at a source pin tuple is a genuine unital monoid character. -/
def sourcePinCharacter (a : V → A) : jointMonoid (V := V) L g →* K where
  toFun p := p.val.1 a
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Evaluation at a target pin tuple on the very same joint monoid. -/
def targetPinCharacter (b : V → B) : jointMonoid (V := V) L g →* K where
  toFun p := p.val.2 b
  map_one' := rfl
  map_mul' _ _ := rfl

omit [CharZero K] in
/-- Equality of the two evaluation characters is exactly universal equality on
all common instance templates, including arbitrary finite hidden-variable types. -/
theorem pinCharacter_eq_iff (a : V → A) (b : V → B) :
    sourcePinCharacter L g a = targetPinCharacter L g b ↔ AllPinnedEqual L g a b := by
  constructor
  · intro he H hH dH I
    exact congrArg (fun χ : jointMonoid (V := V) L g →* K => χ (jointElement L g I)) he
  · intro he
    ext p
    rcases p.property with ⟨n, I, hI⟩
    change p.val.1 a = p.val.2 b
    rw [hI]
    exact he (Fin n) I

omit [CharZero K] in
/-- Boundary substitution preserves equality on all instances, using the actual
scope-renaming construction. Repeated variables are retained by that construction. -/
theorem allPinnedEqual_comp {W : Type} (a : V → A) (b : V → B)
    (h : AllPinnedEqual L g a b) (f : W → V) :
    AllPinnedEqual L g (a ∘ f) (b ∘ f) := by
  intro H hH dH I
  have he := h H (I.renameBoundary f)
  rw [Instance.retarget_renameBoundary, Instance.partition_renameBoundary,
    Instance.partition_renameBoundary] at he
  exact he

omit [CharZero K] in
/-- Source-side pin twins give equality as characters on the joint monoid. -/
theorem source_character_eq_of_twins (a a' : V → A)
    (hp : ∀ v, L.Twins (a v) (a' v)) :
    sourcePinCharacter L g a = sourcePinCharacter L g a' := by
  ext p
  rcases p.property with ⟨n, I, hI⟩
  change p.val.1 a = p.val.1 a'
  rw [hI]
  exact I.partition_eq_of_pin_twins a a' hp

omit [CharZero K] in
/-- Target-side pin twins give equality as characters on the same joint monoid. -/
theorem target_character_eq_of_twins (b b' : V → B)
    (hp : ∀ v, (L.retarget g).Twins (b v) (b' v)) :
    targetPinCharacter L g b = targetPinCharacter L g b' := by
  ext p
  rcases p.property with ⟨n, I, hI⟩
  change p.val.2 b = p.val.2 b'
  rw [hI]
  exact (I.retarget g).partition_eq_of_pin_twins b b' hp

variable [Fintype T] [DecidableEq T]

omit [CharZero K] in
/-- Unlabeling the extension variables in every shared witness equates sums
of extension characters from universally equal old pins. -/
theorem extension_character_sums_eq (a : V → A) (b : V → B)
    (h : AllPinnedEqual L g a b) (p : jointMonoid (V := V ⊕ T) L g) :
    (∑ x : T → A, sourcePinCharacter L g (Sum.elim a x) p) =
      ∑ y : T → B, targetPinCharacter L g (Sum.elim b y) p := by
  rcases p.property with ⟨n, I, hI⟩
  change (∑ x : T → A, p.val.1 (Sum.elim a x)) =
    ∑ y : T → B, p.val.2 (Sum.elim b y)
  rw [hI]
  have he := h (T ⊕ Fin n) I.hideBoundary
  rw [Instance.retarget_hideBoundary, Instance.partition_hideBoundary,
    Instance.partition_hideBoundary] at he
  exact he

/-- Each joint character class has the same finite extension multiplicity on
both sides. Natural cardinality keeps equality decidability out of the interface. -/
theorem extension_character_multiplicities_eq (a : V → A) (b : V → B)
    (h : AllPinnedEqual L g a b) (ρ : jointMonoid (V := V ⊕ T) L g →* K) :
    Nat.card {x : T → A // sourcePinCharacter L g (Sum.elim a x) = ρ} =
      Nat.card {y : T → B // targetPinCharacter L g (Sum.elim b y) = ρ} := by
  classical
  simpa only [Nat.card_eq_fintype_card] using character_multiplicities_eq
    (fun x : T → A => sourcePinCharacter L g (Sum.elim a x))
    (fun y : T → B => targetPinCharacter L g (Sum.elim b y))
    (extension_character_sums_eq L g a b h) ρ

/-- Every prescribed finite extension of one pin tuple has a matching extension
of the other which remains equal on **all** finite instances. No matching
extension or target isomorphism is assumed as a conclusion-premise. -/
theorem exists_pinned_extension (a : V → A) (b : V → B)
    (h : AllPinnedEqual L g a b) (x : T → A) :
    ∃ y : T → B, AllPinnedEqual L g (Sum.elim a x) (Sum.elim b y) := by
  obtain ⟨y, hy⟩ := exists_matching_character
    (fun x : T → A => sourcePinCharacter L g (Sum.elim a x))
    (fun y : T → B => targetPinCharacter L g (Sum.elim b y))
    (extension_character_sums_eq L g a b h) x
  refine ⟨y, ?_⟩
  intro H hH dH I
  exact congrArg (fun χ : jointMonoid (V := V ⊕ T) L g →* K => χ (jointElement L g I)) hy

/-- For surjective pin tuples, corresponding twin classes have equal cardinality.
The proof counts actual extension-character fibers, and extracts twins through
one-constraint diagrams; neither class equality nor an isomorphism is assumed. -/
theorem twin_class_card_eq_of_allPinnedEqual (a : V → A) (b : V → B)
    (h : AllPinnedEqual L g a b) (ha : Function.Surjective a) (hb : Function.Surjective b)
    (v : V) :
    Nat.card {x : A // L.Twins x (a v)} =
      Nat.card {y : B // (L.retarget g).Twins y (b v)} := by
  classical
  let ax : Unit → A := fun _ => a v
  let by' : Unit → B := fun _ => b v
  let f : V ⊕ Unit → V := Sum.elim id (fun _ => v)
  have heA : a ∘ f = Sum.elim a ax := by funext z; cases z <;> rfl
  have heB : b ∘ f = Sum.elim b by' := by funext z; cases z <;> rfl
  have hclone : AllPinnedEqual L g (Sum.elim a ax) (Sum.elim b by') := by
    simpa only [heA, heB] using allPinnedEqual_comp L g a b h f
  have hcloneChar := (pinCharacter_eq_iff L g (Sum.elim a ax) (Sum.elim b by')).mpr hclone
  let ρ : jointMonoid (V := V ⊕ Unit) L g →* K :=
    sourcePinCharacter L g (Sum.elim a ax)
  have hsource (x : Unit → A) :
      sourcePinCharacter L g (Sum.elim a x) = ρ ↔ L.Twins (x ()) (a v) := by
    constructor
    · intro hx
      have he := (pinCharacter_eq_iff L g (Sum.elim a x) (Sum.elim b by')).mp
        (hx.trans hcloneChar)
      have hd := sameAtomicDiagram_of_allPinnedEqual L g _ _ he
      have has : Function.Surjective (Sum.elim a x) := by
        intro u; obtain ⟨w, hw⟩ := ha u; exact ⟨Sum.inl w, hw⟩
      have hbs : Function.Surjective (Sum.elim b by') := by
        intro u; obtain ⟨w, hw⟩ := hb u; exact ⟨Sum.inl w, hw⟩
      exact (twins_iff_of_surjective_diagram L g _ _ hd has hbs (Sum.inr ()) (Sum.inl v)).mpr
        ((L.retarget g).twins_refl _)
    · intro hx
      apply source_character_eq_of_twins L g
      intro z
      cases z with
      | inl w => exact L.twins_refl _
      | inr u => cases u; exact hx
  have htarget (y : Unit → B) :
      targetPinCharacter L g (Sum.elim b y) = ρ ↔ (L.retarget g).Twins (y ()) (b v) := by
    constructor
    · intro hy
      have he := (pinCharacter_eq_iff L g (Sum.elim a ax) (Sum.elim b y)).mp hy.symm
      have hd := sameAtomicDiagram_of_allPinnedEqual L g _ _ he
      have hbs : Function.Surjective (Sum.elim b y) := by
        intro u; obtain ⟨w, hw⟩ := hb u; exact ⟨Sum.inl w, hw⟩
      exact twins_transfer_of_diagram L g _ _ hd hbs
        (v := Sum.inr ()) (w := Sum.inl v) (L.twins_refl _)
    · intro hy
      apply Eq.trans _ hcloneChar.symm
      apply target_character_eq_of_twins L g
      intro z
      cases z with
      | inl w => exact (L.retarget g).twins_refl _
      | inr u => cases u; exact hy
  let es : {x : Unit → A // sourcePinCharacter L g (Sum.elim a x) = ρ} ≃
      {x : A // L.Twins x (a v)} :=
    Equiv.subtypeEquiv (Equiv.funUnique Unit A) hsource
  let et : {y : Unit → B // targetPinCharacter L g (Sum.elim b y) = ρ} ≃
      {y : B // (L.retarget g).Twins y (b v)} :=
    Equiv.subtypeEquiv (Equiv.funUnique Unit B) htarget
  exact (Nat.card_congr es).symm.trans
    ((extension_character_multiplicities_eq L g a b h ρ).trans (Nat.card_congr et))

end
end PinnedIsomorphism
end ComplexCSP
