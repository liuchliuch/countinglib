import ComplexCSP.Instances.PinnedIsomorphism
import ComplexCSP.Structure.CharacterIndependence
import Mathlib.Algebra.FreeMonoid.Basic

/-! # All-instance isomorphism with a twin-free source

Equality quantifies over every finite instance, retaining repeated constraints
and repeated scope positions. IsomorphismCompleteness proves the general case
with twin multiplicities. -/

set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP.PinnedIsomorphism

open scoped BigOperators

section CharacterMultiplicity

variable {M K A B : Type*} [Monoid M] [Field K] [CharZero K]
variable [Fintype A] [Fintype B]

/-- Equal sums of characters determine the multiplicity of every character.
Unlike distinct-character independence, this retains repeated equal summands. -/
theorem character_multiplicities_eq [DecidableEq (M →* K)] (χ : A → M →* K) (ψ : B → M →* K)
    (h : ∀ x, ∑ a, χ a x = ∑ b, ψ b x) (ρ : M →* K) :
    Fintype.card {a // χ a = ρ} = Fintype.card {b // ψ b = ρ} := by
  classical
  let ξ : A ⊕ B → M →* K := Sum.elim χ ψ
  let c : A ⊕ B → K := Sum.elim (fun _ => 1) (fun _ => -1)
  have hzero : ∀ x, ∑ i : A ⊕ B, c i * ξ i x = 0 := by
    intro x
    simp only [Fintype.sum_sum_type, c, ξ, Sum.elim_inl, Sum.elim_inr,
      one_mul, neg_one_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero]
    exact h x
  have hcoef : characterClassCoefficient Finset.univ ξ c ρ = 0 := by
    by_cases hr : ρ ∈ characterClasses Finset.univ ξ
    · exact (grouped_character_zero_iff Finset.univ ξ c).mp hzero ρ hr
    · have hempty : (Finset.univ.filter fun i => ξ i = ρ) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro i hi
        apply hr
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (Finset.mem_filter.mp hi).2⟩
      simp only [characterClassCoefficient, hempty, Finset.sum_empty]
  have hneg : (∑ b, if ψ b = ρ then (-1 : K) else 0) =
      -(Fintype.card {b // ψ b = ρ} : K) := by
    simp_rw [show ∀ b, (if ψ b = ρ then (-1 : K) else 0) =
      -(if ψ b = ρ then (1 : K) else 0) from fun b => by split_ifs <;> simp]
    simp [Fintype.card_subtype]
  have hc : (Fintype.card {a // χ a = ρ} : K) -
      (Fintype.card {b // ψ b = ρ} : K) = 0 := by
    simp only [characterClassCoefficient, Finset.sum_filter, Fintype.sum_sum_type,
      ξ, c, Sum.elim_inl, Sum.elim_inr] at hcoef
    rw [hneg] at hcoef
    simpa [Fintype.card_subtype, sub_eq_add_neg] using hcoef
  exact Nat.cast_injective (sub_eq_zero.mp hc)

/-- Every individual character appearing on one side has a matching character
on the other side. Characteristic zero rules out cancellation of positive counts. -/
theorem exists_matching_character (χ : A → M →* K) (ψ : B → M →* K)
    (h : ∀ x, ∑ a, χ a x = ∑ b, ψ b x) (a : A) :
    ∃ b, χ a = ψ b := by
  classical
  have he := character_multiplicities_eq χ ψ h (χ a)
  have hpos : 0 < Fintype.card {a' // χ a' = χ a} :=
    Fintype.card_pos_iff.mpr ⟨⟨a, rfl⟩⟩
  rw [he] at hpos
  obtain ⟨b, hb⟩ := Fintype.card_pos_iff.mp hpos
  exact ⟨b, hb.symm⟩

end CharacterMultiplicity

section AtomicExtraction

variable {A B K ι V H : Type} [Field K] [CharZero K]
variable [Fintype A] [Fintype B] [Fintype H] [DecidableEq H]
variable (L : Language A K ι)
variable (g : (i : ι) → (Fin (L.arity i) → B) → K)

/-- The exact all-instance hypothesis, including all finite
hidden-variable types and all repeated constraints/scopes. -/
def AllPinnedEqual (a : V → A) (b : V → B) : Prop :=
  ∀ (H : Type) [Fintype H] [DecidableEq H], ∀ I : Instance L V H,
    I.partition a = (I.retarget g).partition b

/-- An assignment gives a character on finite words of literal constraint atoms. -/
def atomicCharacter (a : V → A) (x : H → A) :
    FreeMonoid (Constraint L (V ⊕ H)) →* K :=
  FreeMonoid.lift (fun c => c.eval (Sum.elim a x))

/-- Evaluate the same alphabet using the arity-matched target tables. -/
def targetAtomicCharacter (b : V → B) (y : H → B) :
    FreeMonoid (Constraint L (V ⊕ H)) →* K :=
  FreeMonoid.lift (fun c => g c.symbol (Sum.elim b y ∘ c.scope))

omit [CharZero K] in
/-- Universal equality of actual instances yields equality of sums of actual
assignment characters, with one summand per hidden-variable assignment. -/
theorem atomic_character_sums_eq (a : V → A) (b : V → B)
    (h : AllPinnedEqual L g a b) (w : FreeMonoid (Constraint L (V ⊕ H))) :
    (∑ x : H → A, atomicCharacter L a x w) =
      ∑ y : H → B, targetAtomicCharacter L g b y w := by
  have hw := h H (⟨w.toList⟩ : Instance L V H)
  simpa only [Instance.partition, Instance.eval, Instance.retarget, List.map_map,
    atomicCharacter, targetAtomicCharacter, FreeMonoid.lift_apply,
    Constraint.eval, Language.retarget, Function.comp_def] using hw

/-- Each complete source assignment has a target assignment with exactly the
same complete atomic diagram, even for arbitrary arities and unary symbols. -/
theorem exists_atomic_extension (a : V → A) (b : V → B)
    (h : AllPinnedEqual L g a b) (x : H → A) :
    ∃ y : H → B, ∀ (i : ι) (s : Fin (L.arity i) → V ⊕ H),
      L.value i (Sum.elim a x ∘ s) = g i (Sum.elim b y ∘ s) := by
  obtain ⟨y, hy⟩ := exists_matching_character
    (atomicCharacter L a) (targetAtomicCharacter L g b)
    (atomic_character_sums_eq L g a b h) x
  refine ⟨y, ?_⟩
  intro i s
  have he := congrArg (fun z : FreeMonoid (Constraint L (V ⊕ H)) →* K =>
    z (FreeMonoid.of ⟨i, s⟩)) hy
  simpa [atomicCharacter, targetAtomicCharacter, Constraint.eval] using he

/-- Isolated hidden variables force equality of target domain cardinalities. -/
theorem target_card_eq_of_allPinnedEqual (a : V → A) (b : V → B)
    (h : AllPinnedEqual L g a b) : Fintype.card A = Fintype.card B := by
  have hc := h Unit (⟨[]⟩ : Instance L V Unit)
  have he : (Fintype.card A : K) = (Fintype.card B : K) := by
    simpa [Instance.partition, Instance.eval, Instance.retarget] using hc
  exact Nat.cast_injective he

end AtomicExtraction

section FiniteDiagrams

variable {A B K ι V : Type} [Field K] [CharZero K]
variable [Fintype A] [Fintype B]
variable (L : Language A K ι)
variable (g : (i : ι) → (Fin (L.arity i) → B) → K)

/-- Equality of every atomic table entry addressed by the pinned variable tuple. -/
def SameAtomicDiagram (a : V → A) (b : V → B) : Prop :=
  ∀ (i : ι) (s : Fin (L.arity i) → V), L.value i (a ∘ s) = g i (b ∘ s)

/-- One-constraint instances, with all variables pinned, recover the full atomic
diagram. Repeated scope positions are deliberately permitted here. -/
theorem sameAtomicDiagram_of_allPinnedEqual (a : V → A) (b : V → B)
    (h : AllPinnedEqual L g a b) : SameAtomicDiagram L g a b := by
  intro i s
  have hv := h (Fin 0) (⟨[⟨i, Sum.inl ∘ s⟩]⟩ : Instance L V (Fin 0))
  simpa [Instance.partition, Instance.eval, Instance.retarget, Constraint.eval,
    Function.comp_def, Language.retarget] using hv

/-- A matching full-domain atomic assignment preserves every original table. -/
theorem preserves_tables_of_atomic_extension (a : V → A) (b : V → B) (f : A → B)
    (h : ∀ (i : ι) (s : Fin (L.arity i) → V ⊕ A),
      L.value i (Sum.elim a id ∘ s) = g i (Sum.elim b f ∘ s)) :
    ∀ (i : ι) (x : Fin (L.arity i) → A), L.value i x = g i (f ∘ x) := by
  intro i x
  simpa [Function.comp_def] using h i (Sum.inr ∘ x)

/-- The kernel of a full table-preserving map consists only of source twins. -/
theorem twins_of_preserving_map_eq (f : A → B)
    (hf : ∀ (i : ι) (x : Fin (L.arity i) → A), L.value i x = g i (f ∘ x))
    {a a' : A} (he : f a = f a') : L.Twins a a' := by
  intro i j x
  rw [hf, hf, Function.comp_update, Function.comp_update, he]

/-- A bijective full-domain atomic extension matches every original pin up to twins. -/
theorem pin_twins_of_atomic_extension (a : V → A) (b : V → B) (e : A ≃ B)
    (h : ∀ (i : ι) (s : Fin (L.arity i) → V ⊕ A),
      L.value i (Sum.elim a id ∘ s) = g i (Sum.elim b e ∘ s)) :
    ∀ v, (L.retarget g).Twins (e (a v)) (b v) := by
  classical
  have ht := preserves_tables_of_atomic_extension L g a b e h
  intro v i j x
  let s : Fin (L.arity i) → V ⊕ A :=
    Function.update (fun t => Sum.inr (e.symm (x t))) j (Sum.inl v)
  have hh := h i s
  rw [ht] at hh
  have hleft : e ∘ (Sum.elim a id ∘ s) = Function.update x j (e (a v)) := by
    funext t
    by_cases htj : t = j
    · subst t
      simp [s, Function.comp_def]
    · simp [s, Function.comp_def, Function.update_of_ne htj]
  have hright : Sum.elim b e ∘ s = Function.update x j (b v) := by
    funext t
    by_cases htj : t = j
    · subst t
      simp [s, Function.comp_def]
    · simp [s, Function.comp_def, Function.update_of_ne htj]
  simpa only [hleft, hright, Language.retarget] using hh

/-- All-instance completeness with a twin-free source. The general theorem
with twin multiplicities is proved in IsomorphismCompleteness. -/
theorem all_instance_completeness_twinFree_source
    (a : V → A) (b : V → B)
    (htwin : ∀ x y, L.Twins x y → x = y)
    (h : AllPinnedEqual L g a b) :
    ∃ e : A ≃ B, L.IsTargetIso g e ∧
      ∀ v, (L.retarget g).Twins (e (a v)) (b v) := by
  classical
  obtain ⟨f, hf⟩ := exists_atomic_extension L g a b h (id : A → A)
  have htable := preserves_tables_of_atomic_extension L g a b f hf
  have hinj : Function.Injective f := fun x y hxy =>
    htwin x y (twins_of_preserving_map_eq L g f htable hxy)
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hinj, target_card_eq_of_allPinnedEqual L g a b h⟩
  let e : A ≃ B := Equiv.ofBijective f hbij
  refine ⟨e, htable, ?_⟩
  exact pin_twins_of_atomic_extension L g a b e hf

end FiniteDiagrams

end ComplexCSP.PinnedIsomorphism
