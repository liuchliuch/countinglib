import ComplexCSP.Structure.MaltsevRelations

/-!
# Original-table row equivalence and Type Partition

Actual nonzero complex rows are quotiented by nonzero scalar proportionality.
Their classes are proved disjoint, and their union-of-products relation is
proved to be precisely nonzero proportional-row equivalence. The last theorem
specializes the Section 9.1 proof to finite-prefix types of an original complex
table, without assuming a supplied row partition.
-/
namespace ComplexCSP
namespace RowTypes

open MaltsevRelations

universe u v w

/-- Nonzero scalar proportionality of two vectors. -/
def Proportional {𝕜 : Type u} [Field 𝕜] {J : Type v}
    (x y : J → 𝕜) : Prop := ∃ c : 𝕜, c ≠ 0 ∧ ∀ j, x j = c * y j

theorem proportional_refl {𝕜 : Type u} [Field 𝕜] {J : Type v} (x : J → 𝕜) :
    Proportional x x := ⟨1, one_ne_zero, by simp⟩

theorem proportional_symm {𝕜 : Type u} [Field 𝕜] {J : Type v}
    {x y : J → 𝕜} (h : Proportional x y) : Proportional y x := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  intro j
  rw [h j]
  simp [hc]

theorem proportional_trans {𝕜 : Type u} [Field 𝕜] {J : Type v}
    {x y z : J → 𝕜} (hxy : Proportional x y) (hyz : Proportional y z) :
    Proportional x z := by
  obtain ⟨c, hc, hxy⟩ := hxy
  obtain ⟨d, hd, hyz⟩ := hyz
  exact ⟨c * d, mul_ne_zero hc hd, fun j => by rw [hxy j, hyz j, mul_assoc]⟩

/-- The row equivalence from the paper excludes zero rows on both sides. -/
def NonzeroProportionalRows {𝕜 : Type u} [Field 𝕜] {X : Type v} {J : Type w}
    (G : X → J → 𝕜) (x y : X) : Prop :=
  G x ≠ 0 ∧ G y ≠ 0 ∧ Proportional (G x) (G y)

def rowSetoid {𝕜 : Type u} [Field 𝕜] {X : Type v} {J : Type w}
    (G : X → J → 𝕜) : Setoid {x : X // G x ≠ 0} where
  r x y := Proportional (G x.val) (G y.val)
  iseqv := ⟨fun x => proportional_refl (G x.val),
    fun {_ _} h => proportional_symm h,
    fun {_ _ _} h₁ h₂ => proportional_trans h₁ h₂⟩

abbrev RowLabel {𝕜 : Type u} [Field 𝕜] {X : Type v} {J : Type w}
    (G : X → J → 𝕜) := Quotient (rowSetoid G)

/-- Original complex row classes, labeled by their projective equivalence class. -/
def rowClasses {𝕜 : Type u} [Field 𝕜] {X : Type v} {J : Type w}
    (G : X → J → 𝕜) (label : RowLabel G) : Set X :=
  {x | ∃ hx : G x ≠ 0, Quotient.mk (rowSetoid G) ⟨x, hx⟩ = label}

theorem rowClasses_disjoint {𝕜 : Type u} [Field 𝕜]
    {D : Type v} {I : Type w} {J : Type*} (G : (I → D) → J → 𝕜) :
    DisjointClasses (rowClasses G) := by
  intro j k x hx hy
  obtain ⟨hx, hj⟩ := hx
  obtain ⟨hy, hk⟩ := hy
  exact hj.symm.trans hk

/-- The existential union of class products is exactly the original-row
nonzero proportionality relation, in both directions. -/
theorem rowEquivalence_iff {𝕜 : Type u} [Field 𝕜]
    {D : Type v} {I : Type w} {J : Type*} (G : (I → D) → J → 𝕜)
    (x y : I → D) :
    RowEquivalence (rowClasses G) x y ↔ NonzeroProportionalRows G x y := by
  constructor
  · rintro ⟨label, ⟨hx, hxq⟩, ⟨hy, hyq⟩⟩
    exact ⟨hx, hy, Quotient.exact (hxq.trans hyq.symm)⟩
  · rintro ⟨hx, hy, hxy⟩
    refine ⟨Quotient.mk (rowSetoid G) ⟨x, hx⟩, ⟨hx, rfl⟩, hy, ?_⟩
    exact (Quotient.sound hxy).symm

/-- If the actual nonzero-proportional-row relation is preserved, the classes
it determines satisfy Type Partition. No row representation is assumed. -/
theorem table_row_equivalence_forces_type_partition
    {𝕜 : Type u} [Field 𝕜] {D : Type v} {I : Type w} {J : Type*} {K : Type*}
    (G : (I → D) → J → 𝕜) {m : Operation D} (hm : IsMaltsev m)
    (hpres : ∀ x₁ x₂ y₁ y₂ z₁ z₂,
      NonzeroProportionalRows G x₁ x₂ → NonzeroProportionalRows G y₁ y₂ →
      NonzeroProportionalRows G z₁ z₂ →
      NonzeroProportionalRows G (map₃ m x₁ y₁ z₁) (map₃ m x₂ y₂ z₂))
    (ρ : K → I) (α β : K → D) :
    RowType (rowClasses G) ρ α = RowType (rowClasses G) ρ β ∨
      Disjoint (RowType (rowClasses G) ρ α) (RowType (rowClasses G) ρ β) := by
  apply row_equivalence_forces_type_partition (rowClasses_disjoint G) hm
  intro x₁ x₂ y₁ y₂ z₁ z₂ hx hy hz
  apply (rowEquivalence_iff G _ _).mpr
  exact hpres x₁ x₂ y₁ y₂ z₁ z₂
    ((rowEquivalence_iff G _ _).mp hx) ((rowEquivalence_iff G _ _).mp hy)
    ((rowEquivalence_iff G _ _).mp hz)

/-! ## Literal finite-arity complex tables -/

/-- The row indexed by `x` is obtained by retaining the last coordinate. -/
def tableRows {D : Type u} {n : ℕ} (G : (Fin (n + 1) → D) → ℂ)
    (x : Fin n → D) : D → ℂ := fun z => G (Fin.snoc x z)

abbrev TableRowLabel {D : Type u} {n : ℕ} (G : (Fin (n + 1) → D) → ℂ) :=
  RowLabel (tableRows G)

noncomputable instance tableRowLabelFintype {D : Type u} [Fintype D] {n : ℕ}
    (G : (Fin (n + 1) → D) → ℂ) : Fintype (TableRowLabel G) :=
  Fintype.ofFinite _

/-- `Ω_G`, on pairs of row indices. -/
def Omega {D : Type u} {n : ℕ} (G : (Fin (n + 1) → D) → ℂ)
    (x y : Fin n → D) : Prop := NonzeroProportionalRows (tableRows G) x y

/-- The exact prefix type of length `ℓ ≤ n`; `ℓ = 0` and zero tables are allowed. -/
def prefixType {D : Type u} {n : ℕ} (G : (Fin (n + 1) → D) → ℂ)
    {ℓ : ℕ} (hℓ : ℓ ≤ n) (α : Fin ℓ → D) : Set (TableRowLabel G) :=
  RowType (rowClasses (tableRows G)) (Fin.castLE hℓ) α

/-- All prefix types of a finite-domain table are genuinely finite sets. -/
theorem prefixType_finite {D : Type u} [Fintype D] {n : ℕ}
    (G : (Fin (n + 1) → D) → ℂ) {ℓ : ℕ} (hℓ : ℓ ≤ n) (α : Fin ℓ → D) :
    (prefixType G hℓ α).Finite := Set.toFinite _

/-- The empty-prefix type contains every nonzero row-class label, as stipulated
in the paper. This is proved from quotient representatives, not postulated. -/
theorem prefixType_empty_eq_univ {D : Type u} {n : ℕ}
    (G : (Fin (n + 1) → D) → ℂ) (α : Fin 0 → D) :
    prefixType G (Nat.zero_le n) α = Set.univ := by
  apply Set.eq_univ_of_forall
  intro label
  refine Quotient.inductionOn label ?_
  intro x
  exact ⟨x.val, ⟨x.property, rfl⟩, fun i => Fin.elim0 i⟩

/-- A zero table has no nonzero row classes and all of its prefix types are
empty, including the empty prefix. -/
theorem prefixType_zero {D : Type u} {n : ℕ} {ℓ : ℕ}
    (hℓ : ℓ ≤ n) (α : Fin ℓ → D) :
    prefixType (fun _ : Fin (n + 1) → D => (0 : ℂ)) hℓ α = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro label hlabel
  obtain ⟨x, ⟨hx, _⟩, _⟩ := hlabel
  exact hx rfl

/-- The numerical-arity relation `Ω_G ⊆ D^(2n)`, with the two row indices
concatenated in the paper's displayed order. -/
def omegaRelation {D : Type u} {n : ℕ} (G : (Fin (n + 1) → D) → ℂ) :
    Relation D where
  arity := n + n
  tuples := {w | Omega G (fun i => w (Fin.castAdd n i)) (fun i => w (Fin.natAdd n i))}

/-- Ordinary polymorphism preservation of `Ω_G` implies the pairwise row
preservation used in the coordinate calculation. -/
theorem preserves_omega_pairs {D : Type u} {n : ℕ}
    (G : (Fin (n + 1) → D) → ℂ) {m : Operation D}
    (h : Preserves m (omegaRelation G).tuples) :
    ∀ x₁ x₂ y₁ y₂ z₁ z₂,
      Omega G x₁ x₂ → Omega G y₁ y₂ → Omega G z₁ z₂ →
      Omega G (map₃ m x₁ y₁ z₁) (map₃ m x₂ y₂ z₂) := by
  intro x₁ x₂ y₁ y₂ z₁ z₂ hx hy hz
  have hmem (a b : Fin n → D) (hab : Omega G a b) :
      (Fin.addCases a b) ∈ (omegaRelation G).tuples := by
    change Omega G (fun i => Fin.addCases a b (Fin.castAdd n i))
      (fun i => Fin.addCases a b (Fin.natAdd n i))
    simpa only [Fin.addCases_left, Fin.addCases_right] using hab
  have hp := h (Fin.addCases x₁ x₂) (hmem x₁ x₂ hx)
    (Fin.addCases y₁ y₂) (hmem y₁ y₂ hy)
    (Fin.addCases z₁ z₂) (hmem z₁ z₂ hz)
  change Omega G (fun i => map₃ m (Fin.addCases x₁ x₂) (Fin.addCases y₁ y₂)
    (Fin.addCases z₁ z₂) (Fin.castAdd n i))
    (fun i => map₃ m (Fin.addCases x₁ x₂) (Fin.addCases y₁ y₂)
      (Fin.addCases z₁ z₂) (Fin.natAdd n i)) at hp
  simp only [map₃, Fin.addCases_left, Fin.addCases_right] at hp
  exact hp

/-- Lemma 9.1 for an actual original complex table and its literal `2n`-ary row
equivalence relation. This includes every prefix length required in the paper. -/
theorem complex_type_partition {D : Type u} {n : ℕ}
    (G : (Fin (n + 1) → D) → ℂ) {m : Operation D} (hm : IsMaltsev m)
    (h : Preserves m (omegaRelation G).tuples)
    {ℓ : ℕ} (hℓ : ℓ ≤ n) (α β : Fin ℓ → D) :
    prefixType G hℓ α = prefixType G hℓ β ∨
      Disjoint (prefixType G hℓ α) (prefixType G hℓ β) := by
  exact table_row_equivalence_forces_type_partition (tableRows G) hm
    (preserves_omega_pairs G h) (Fin.castLE hℓ) α β

end RowTypes
end ComplexCSP
