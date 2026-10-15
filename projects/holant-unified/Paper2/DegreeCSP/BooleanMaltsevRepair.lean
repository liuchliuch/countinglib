import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Finset.Image

/-! Finite equality-free relation repair, adapted from the local
ComplexCSP/Structure/MaltsevRelations.lean. Every input is an explicit
missing-corner property; common operations are constructed by finite repair
and finite candidate compactness, without an assumed polymorphism provider. -/
namespace Paper2.DegreeCSP.BooleanMaltsevRepair

universe u v w


abbrev Cell (D : Type u) := D × D × D
abbrev Operation (D : Type u) := Cell D → D

def first {D : Type u} : Operation D := fun x => x.1
def second {D : Type u} : Operation D := fun x => x.2.1
def third {D : Type u} : Operation D := fun x => x.2.2

def IsMaltsev {D : Type u} (m : Operation D) : Prop :=
  (∀ a b, m (a, b, b) = a) ∧ (∀ a b, m (b, b, a) = a)

def map₃ {D : Type u} {I : Type v} (m : Operation D)
    (x y z : I → D) : I → D := fun i => m (x i, y i, z i)

def Preserves {D : Type u} {I : Type v} (m : Operation D)
    (R : Set (I → D)) : Prop :=
  ∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, map₃ m x y z ∈ R

structure Relation (D : Type u) where
  arity : ℕ
  tuples : Set (Fin arity → D)

def CommonPolymorphism {D : Type u} (Δ : Set (Relation D))
    (m : Operation D) : Prop := ∀ R ∈ Δ, Preserves m R.tuples

theorem first_preserves {D : Type u} {I : Type v} (R : Set (I → D)) :
    Preserves first R := by
  intro x hx y hy z hz
  exact hx

theorem second_preserves {D : Type u} {I : Type v} (R : Set (I → D)) :
    Preserves second R := by
  intro x hx y hy z hz
  exact hy

theorem third_preserves {D : Type u} {I : Type v} (R : Set (I → D)) :
    Preserves third R := by
  intro x hx y hy z hz
  exact hz

theorem common_first {D : Type u} (Δ : Set (Relation D)) :
    CommonPolymorphism Δ first := fun R _ => first_preserves R.tuples

theorem common_third {D : Type u} (Δ : Set (Relation D)) :
    CommonPolymorphism Δ third := fun R _ => third_preserves R.tuples

/-- Identifying the second and third arguments preserves every relation. -/
theorem preserves_minor {D : Type u} {I : Type v} {m : Operation D}
    {R : Set (I → D)} (hm : Preserves m R) :
    Preserves (fun x => m (x.1, x.2.1, x.2.1)) R := by
  intro x hx y hy z hz
  exact hm x hx y hy y hy

theorem common_minor {D : Type u} {Δ : Set (Relation D)} {m : Operation D}
    (hm : CommonPolymorphism Δ m) :
    CommonPolymorphism Δ (fun x => m (x.1, x.2.1, x.2.1)) := by
  intro R hR
  exact preserves_minor (hm R hR)

/-- The singleton-coordinate missing-corner condition. -/
def Rectangular {X : Type u} {Y : Type v} (R : X → Y → Prop) : Prop :=
  ∀ x y a b, R x a → R y a → R x b → R y b

/-- Rectangularity is equivalent to the paper's equal-or-disjoint row-support
formulation. Empty fibers are included automatically. -/
theorem rectangular_iff_equal_or_disjoint {X : Type u} {Y : Type v}
    (R : X → Y → Prop) :
    Rectangular R ↔ ∀ x y, {a | R x a} = {a | R y a} ∨
      Disjoint {a | R x a} {a | R y a} := by
  classical
  constructor
  · intro h x y
    by_cases hi : ∃ a, R x a ∧ R y a
    · obtain ⟨a, hxa, hya⟩ := hi
      left
      ext b
      exact ⟨fun hxb => h x y a b hxa hya hxb,
        fun hyb => h y x a b hya hxa hyb⟩
    · right
      rw [Set.disjoint_left]
      intro a hxa hya
      exact hi ⟨a, hxa, hya⟩
  · intro h x y a b hxa hya hxb
    rcases h x y with heq | hdisj
    · change b ∈ {a | R y a}
      rw [← heq]
      exact hxb
    · exact False.elim (Set.disjoint_left.mp hdisj hxa hya)

/-- Existential projection of a relation onto a set of retained cells and one
last cell. The row is an ambient function; only its values on `K` are used. -/
def ProjectLast {I : Type u} {D : Type v} (U : Set (I → D))
    (K : Finset I) (c : I) (row : I → D) (value : D) : Prop :=
  ∃ p ∈ U, (∀ i ∈ K, p i = row i) ∧ p c = value

def RectangularProjections {I : Type u} {D : Type v} (U : Set (I → D)) : Prop :=
  ∀ (K : Finset I) (c : I), c ∉ K → Rectangular (ProjectLast U K c)

/-- The empty-row projection is rectangular without assumptions. Therefore
the paper's rectangularity statement for arity at least two suffices. -/
theorem rectangularProjections_of_nonempty {I : Type u} {D : Type v}
    {U : Set (I → D)}
    (h : ∀ (K : Finset I) (c : I), K.Nonempty → c ∉ K →
      Rectangular (ProjectLast U K c)) : RectangularProjections U := by
  intro K c hc
  by_cases hK : K.Nonempty
  · exact h K c hK hc
  · have hzero : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
    subst K
    intro x y a b _ _ hxb
    obtain ⟨p, hp, _, hpb⟩ := hxb
    exact ⟨p, hp, by simp, hpb⟩

/-- The elementary projection step used for each repair of the operation table. -/
theorem repair {I : Type u} {D : Type v} {U : Set (I → D)}
    (hrect : RectangularProjections U) {K : Finset I} {c : I}
    (hc : c ∉ K) {p q r : I → D} (hp : p ∈ U) (hq : q ∈ U) (hr : r ∈ U)
    (hqr : ∀ i ∈ K, q i = r i) (hqp : q c = p c) :
    ∃ p' ∈ U, (∀ i ∈ K, p' i = p i) ∧ p' c = r c := by
  apply hrect K c hc r p (p c) (r c)
  · exact ⟨q, hq, hqr, hqp⟩
  · exact ⟨p, hp, fun _ _ => rfl, rfl⟩
  · exact ⟨r, hr, fun _ _ => rfl, rfl⟩

/-- Section 7's finite repair construction, expressed on the full operation
 table (unconstrained cells are harmless). Every projection hypothesis is a
literal singleton rectangularity assertion. -/
theorem exists_maltsev_of_rectangular_projections
    {D : Type u} [Fintype D] (Δ : Set (Relation D))
    (hrect : RectangularProjections {m | CommonPolymorphism Δ m}) :
    ∃ m, IsMaltsev m ∧ CommonPolymorphism Δ m := by
  classical
  let A : Finset (Cell D) := Finset.univ.filter fun c => c.1 = c.2.1
  let C : Finset (Cell D) := Finset.univ.filter fun c =>
    c.2.1 = c.2.2 ∧ c.1 ≠ c.2.1
  have construction : ∀ (s : Finset (Cell D)), s ⊆ C →
      ∃ m, CommonPolymorphism Δ m ∧
        (∀ a b, m (a, a, b) = b) ∧ (∀ c ∈ s, m c = c.1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨third, common_third Δ, by simp [third], by simp⟩
    | @insert c s hcs ih =>
      intro hs
      have hcC : c ∈ C := hs (Finset.mem_insert_self c s)
      have hsC : s ⊆ C := fun i hi => hs (Finset.mem_insert_of_mem hi)
      obtain ⟨m, hm, hmA, hmS⟩ := ih hsC
      have hcshape : c.2.1 = c.2.2 ∧ c.1 ≠ c.2.1 :=
        (Finset.mem_filter.mp hcC).2
      let K := A ∪ s
      have hcK : c ∉ K := by
        simp only [K, Finset.mem_union, not_or]
        exact ⟨by simpa [A] using hcshape.2, hcs⟩
      let q : Operation D := fun x => m (x.1, x.2.1, x.2.1)
      have hq : CommonPolymorphism Δ q := common_minor hm
      have hqfirst : ∀ i ∈ K, q i = first i := by
        intro i hi
        rcases Finset.mem_union.mp hi with hi | hi
        · have hieq : i.1 = i.2.1 := (Finset.mem_filter.mp hi).2
          simp only [q, first, hieq]
          exact hmA _ _
        · have hishape : i.2.1 = i.2.2 := (Finset.mem_filter.mp (hsC hi)).2.1
          change m (i.1, i.2.1, i.2.1) = i.1
          rw [show (i.1, i.2.1, i.2.1) = i from Prod.ext rfl (Prod.ext rfl hishape)]
          exact hmS i hi
      have hqc : q c = m c := by
        change m (c.1, c.2.1, c.2.1) = m c
        rw [show (c.1, c.2.1, c.2.1) = c from Prod.ext rfl (Prod.ext rfl hcshape.1)]
      obtain ⟨m', hm', hK, hc'⟩ :=
        repair hrect hcK hm hq (common_first Δ) hqfirst hqc
      refine ⟨m', hm', ?_, ?_⟩
      · intro a b
        rw [hK (a, a, b) (Finset.mem_union_left s (by simp [A]))]
        exact hmA a b
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact hc'
        · rw [hK i (Finset.mem_union_right A hi)]
          exact hmS i hi
  obtain ⟨m, hm, hmA, hmC⟩ := construction C (fun _ h => h)
  refine ⟨m, ⟨?_, ?_⟩, hm⟩
  · intro a b
    by_cases hab : a = b
    · subst a
      exact hmA b b
    · exact hmC (a, b, b) (by simp [C, hab])
  · intro a b
    exact hmA b a

/-- Finite operation compactness: satisfying each finite group of tests implies
that a single candidate satisfies all tests. No compactness axiom is used. -/
theorem finite_candidate_compactness {M : Type u} [Fintype M]
    {J : Type v} (P : M → J → Prop)
    (h : ∀ s : Finset J, ∃ m : M, ∀ j ∈ s, P m j) :
    ∃ m : M, ∀ j, P m j := by
  classical
  by_contra hnone
  have hbad : ∀ m : M, ∃ j : J, ¬ P m j := by
    simpa only [not_exists, not_forall] using hnone
  choose bad hbad using hbad
  obtain ⟨m, hm⟩ := h (Finset.univ.image bad)
  exact hbad m (hm (bad m) (Finset.mem_image.mpr ⟨m, Finset.mem_univ m, rfl⟩))

/-- The quantifier exchange in Section 7.5, specialized to finite operation
 tables and an arbitrary, potentially infinite, relation family. -/
theorem common_maltsev_of_finite_subfamilies {D : Type u} [Fintype D]
    (Γ : Set (Relation D))
    (hfinite : ∀ s : Finset (Relation D), (↑s : Set (Relation D)) ⊆ Γ →
      ∃ m, IsMaltsev m ∧ CommonPolymorphism (↑s : Set (Relation D)) m) :
    ∃ m, IsMaltsev m ∧ CommonPolymorphism Γ m := by
  classical
  let M := {m : Operation D // IsMaltsev m}
  let P : M → Γ → Prop := fun m R => Preserves m.val R.val.tuples
  have h : ∀ s : Finset Γ, ∃ m : M, ∀ R ∈ s, P m R := by
    intro s
    obtain ⟨m, hm, hp⟩ := hfinite (s.image Subtype.val) (by
      intro R hR
      rcases Finset.mem_image.mp hR with ⟨S, _, rfl⟩
      exact S.property)
    refine ⟨⟨m, hm⟩, ?_⟩
    intro R hR
    exact hp R.val (Finset.mem_image.mpr ⟨R, hR, rfl⟩)
  obtain ⟨m, hm⟩ := finite_candidate_compactness P h
  exact ⟨m.val, m.property, fun R hR => hm ⟨R, hR⟩⟩

/-! ## Finite equality-free pp syntax and the universal relation

An atom has a relation and a scope map. Repeated variables are literal repeated
values of the scope map; there are no equality atoms. Existential quantification
is supplied by `ProjectLast`. Thus the following hypothesis is exactly the
singleton rectangularity input used in Section 7, for finite conjunctions and
their coordinate projections.
-/

structure EqualityFreeConjunction (D : Type u) (A : Type v) (V : Type w) where
  relation : A → Relation D
  scope : (a : A) → Fin (relation a).arity → V

def EqualityFreeConjunction.Satisfies
    {D : Type u} {A : Type v} {V : Type w}
    (C : EqualityFreeConjunction D A V) (p : V → D) : Prop :=
  ∀ a, (fun i => p (C.scope a i)) ∈ (C.relation a).tuples

def EqualityFreeConjunction.UsesOnly
    {D : Type u} {A : Type v} {V : Type w}
    (C : EqualityFreeConjunction D A V) (Γ : Set (Relation D)) : Prop :=
  ∀ a, C.relation a ∈ Γ

/-- Every existential projection of a finite equality-free conjunction of
relations in `Γ` has the singleton-coordinate missing-corner property. -/
def EqualityFreeSingletonRectangularity {D : Type u} (Γ : Set (Relation D)) : Prop :=
  ∀ (V A : Type u) [Fintype V] [Fintype A]
    (C : EqualityFreeConjunction D A V), C.UsesOnly Γ →
      RectangularProjections {p | C.Satisfies p}

/-- One atom for every relation and every ordered triple of its tuples. -/
abbrev PreservationTest {D : Type u} (Δ : Finset (Relation D)) :=
  Σ R : {R : Relation D // R ∈ Δ},
    R.val.tuples × R.val.tuples × R.val.tuples

noncomputable instance preservationTestFintype
    {D : Type u} [Fintype D] (Δ : Finset (Relation D)) :
    Fintype (PreservationTest Δ) := by
  classical
  unfold PreservationTest
  infer_instance

/-- The universal polymorphism formula of Section 7.4. Full operation tables
are used as the variable space. Cells outside the paper's `T` occur in no scope
and are therefore unconstrained. -/
def universalConjunction {D : Type u} (Δ : Finset (Relation D)) :
    EqualityFreeConjunction D (PreservationTest Δ) (Cell D) where
  relation t := t.1.val
  scope t i := (t.2.1.val i, t.2.2.1.val i, t.2.2.2.val i)

/-- The universal formula performs exactly all preservation tests. -/
theorem universalConjunction_iff {D : Type u} (Δ : Finset (Relation D))
    (m : Operation D) :
    (universalConjunction Δ).Satisfies m ↔
      CommonPolymorphism (↑Δ : Set (Relation D)) m := by
  constructor
  · intro h R hR x hx y hy z hz
    exact h ⟨⟨R, hR⟩, ⟨x, hx⟩, ⟨y, hy⟩, ⟨z, hz⟩⟩
  · intro h t
    exact h t.1.val t.1.property t.2.1.val t.2.1.property
      t.2.2.1.val t.2.2.1.property t.2.2.2.val t.2.2.2.property

/-- The complete finite-family relational construction in Section 7.4. The
analytic support-realization and Block Orthogonality arguments are separate
inputs yielding `EqualityFreeSingletonRectangularity`. -/
theorem finite_family_maltsev
    {D : Type u} [Fintype D] {Γ : Set (Relation D)}
    (hrect : EqualityFreeSingletonRectangularity Γ)
    (Δ : Finset (Relation D)) (hΔ : (↑Δ : Set (Relation D)) ⊆ Γ) :
    ∃ m, IsMaltsev m ∧ CommonPolymorphism (↑Δ : Set (Relation D)) m := by
  have huses : (universalConjunction Δ).UsesOnly Γ := fun t => hΔ t.1.property
  have hproj := hrect (Cell D) (PreservationTest Δ) (universalConjunction Δ) huses
  have hset : {p | (universalConjunction Δ).Satisfies p} =
      {m | CommonPolymorphism (↑Δ : Set (Relation D)) m} := by
    ext m
    exact universalConjunction_iff Δ m
  rw [hset] at hproj
  exact exists_maltsev_of_rectangular_projections (↑Δ : Set (Relation D)) hproj

/-- Sections 7.4 and 7.5 combined: a single Mal'tsev operation preserves the
entire relation family. Only the finite domain, finite equality-free syntax,
and the explicit missing-corner hypothesis are assumed. -/
theorem common_maltsev_of_equalityfree_rectangularity
    {D : Type u} [Fintype D] (Γ : Set (Relation D))
    (hrect : EqualityFreeSingletonRectangularity Γ) :
    ∃ m, IsMaltsev m ∧ CommonPolymorphism Γ m := by
  apply common_maltsev_of_finite_subfamilies Γ
  intro Δ hΔ
  exact finite_family_maltsev hrect Δ hΔ


end Paper2.DegreeCSP.BooleanMaltsevRepair
