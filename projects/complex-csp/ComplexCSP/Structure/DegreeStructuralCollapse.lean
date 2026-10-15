import ComplexCSP.Recognition.DegreeConditions
import ComplexCSP.Structure.RowEquivalenceRealization
import ComplexCSP.Structure.StructuralCollapse

/-! # Structural collapse for the actual degree-multiple family

Every detector and pp-support witness retains literal occurrence-degree
certificates. The only BO premise is the degree-restricted joint legal condition.
This proves the structural part of Corollary 1.2; no decision procedure or
pinned-isomorphism theorem is used or asserted here.
-/
namespace ComplexCSP
open scoped BigOperators

/-- The literal two-copy row detector retains the degree-multiple restriction. -/
theorem DegreeGenerated.row_detector {D K ι : Type} [CommSemiring K] [Fintype D]
    {L : Language D K ι} {δ n : ℕ} {G : (Fin (n + 1) → D) → K}
    (hG : DegreeGenerated L δ G) (p q : ℕ) :
    DegreeGenerated L δ (rowDetector G p q) := by
  let F := fun a : Fin (n + n) ⊕ Unit → D =>
    G (a ∘ detectorLeftScope n) ^ p * G (a ∘ detectorRightScope n) ^ q
  have hF : DegreeGenerated L δ F :=
    ((hG.diagonal_minor (detectorLeftScope n)).pow p).mul
      ((hG.diagonal_minor (detectorRightScope n)).pow q)
  have hm := hF.marginal_finite
  have he : (fun a => ∑ b : Unit → D, F (Sum.elim a b)) = rowDetector G p q := by
    funext a
    simp only [F, detectorLeft_assignment, detectorRight_assignment, rowDetector]
    exact (Equiv.funUnique Unit D).sum_comp (fun z =>
      G (Fin.snoc (fun i => a (Fin.castAdd n i)) z) ^ p *
      G (Fin.snoc (fun i => a (Fin.natAdd n i)) z) ^ q)
  rwa [he] at hm

namespace DegreeStructuralCollapse
open BlockOrthogonality RowTypes RowPhases RowDetector MaltsevRelations
open Purification PurificationMap RowEquivalenceRealization

/-- Theorem 8.4's concrete detector is generated and realizes the literal
row-equivalence relation. The number field and its torsion exponent are derived
from algebraicity of the finite input language. -/
theorem generated_row_equivalence_detector {D ι : Type} [Fintype D] [Fintype ι]
    (L : Language D ℂ ι) (δ : ℕ) (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a))
    (hBO : DegreeJointBO L δ) {n : ℕ} (hn : 0 < n)
    (G : (Fin (n + 1) → D) → ℂ) (hG : DegreeGenerated L δ G) :
    ∃ E t : ℕ, 2 ≤ E ∧
      DegreeGenerated L δ (rowDetector G
        ((E - 1) * (1 + phaseExponent (Fintype.card D) * t))
        (1 + phaseExponent (Fintype.card D) * t)) ∧
      ∀ a : Fin (n + n) → D,
        rowDetector G ((E - 1) * (1 + phaseExponent (Fintype.card D) * t))
            (1 + phaseExponent (Fintype.card D) * t) a ≠ 0 ↔
          a ∈ (omegaRelation G).tuples := by
  classical
  let T : PositiveTable D := ⟨n, G⟩
  let C := GeneratingSet.LegalGeneratingSet.choose T.nonzeroValues
  have hcontains : GeneratingSet.LegalGeneratingSet.ContainsTable T.nonzeroValues (tableRows G) := by
    intro x z hz
    exact (T.mem_nonzeroValues _).mpr ⟨x, z, rfl⟩
  let P := C.tableMap (tableRows G) hcontains
  have hP : BlockOrthogonal (PurificationMap.purifyTable (tableRows G) P) := by
    exact (degreeJointBO_iff_singletonBO L δ).mp hBO T hG hn
  have hpow : ∀ h, 0 < h → h ≤ Fintype.card D →
      BlockOrthogonal (fun x z => tableRows G x z ^ h) := by
    intro h _ _
    exact hBO.original L δ n (fun a => G a ^ h) (hG.pow h)
  let K : Subfield ℂ := L.workingField.toSubfield
  letI : NumberField K := L.workingField_numberField hAlg
  have hK : ∀ x z, tableRows G x z ∈ K := by
    intro x z
    exact Instance.generated_mem_workingField hG.generated (Fin.snoc x z)
  obtain ⟨t, ht⟩ := exists_detector_support (tableRows G) P hP hpow K hK
  refine ⟨fieldExponent K, t, fieldExponent_ge_two K, hG.row_detector _ _, ?_⟩
  intro a
  exact ht (fun i => a (Fin.castAdd n i)) (fun i => a (Fin.natAdd n i))

/-- The exact Ω relation is a support of an actual generated table. -/
theorem omega_mem_degreeGeneratedSupports {D ι : Type} [Fintype D] [Fintype ι]
    (L : Language D ℂ ι) (δ : ℕ) (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a))
    (hBO : DegreeJointBO L δ) {n : ℕ} (hn : 0 < n)
    (G : (Fin (n + 1) → D) → ℂ) (hG : DegreeGenerated L δ G) :
    omegaRelation G ∈ degreeGeneratedSupports L δ := by
  obtain ⟨E, t, _, hdet, hsupp⟩ := generated_row_equivalence_detector L δ hAlg hBO hn G hG
  refine ⟨rowDetector G ((E - 1) * (1 + phaseExponent (Fintype.card D) * t))
      (1 + phaseExponent (Fintype.card D) * t), hdet, ?_⟩
  ext a
  exact (hsupp a).symm

/-- One operation simultaneously preserves every actual generated support and
every applicable original-table Ω relation. This is the common operation
required in the structural conclusion, not a separate operation per table. -/
theorem common_support_and_row_maltsev {D ι : Type} [Fintype D] [Nonempty D] [Fintype ι]
    (L : Language D ℂ ι) (δ : ℕ) (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) (hBO : DegreeJointBO L δ) :
    ∃ m : MaltsevRelations.Operation D, MaltsevRelations.IsMaltsev m ∧
      MaltsevRelations.CommonPolymorphism (degreeGeneratedSupports L δ) m ∧
      ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n + 1) → D) → ℂ),
        DegreeGenerated L δ G → MaltsevRelations.Preserves m (omegaRelation G).tuples := by
  obtain ⟨m, hm, hsupp⟩ := hBO.common_support_maltsev L δ
  exact ⟨m, hm, hsupp, fun n hn G hG =>
    hsupp (omegaRelation G) (omega_mem_degreeGeneratedSupports L δ hAlg hBO hn G hG)⟩

/-- The Type Partition half of the structural collapse for every original
generated complex table and every actual prefix length. -/
theorem generated_type_partition {D ι : Type} [Fintype D] [Nonempty D] [Fintype ι]
    (L : Language D ℂ ι) (δ : ℕ) (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) (hBO : DegreeJointBO L δ)
    {n : ℕ} (hn : 0 < n) (G : (Fin (n + 1) → D) → ℂ) (hG : DegreeGenerated L δ G)
    {ℓ : ℕ} (hℓ : ℓ ≤ n) (α β : Fin ℓ → D) :
    prefixType G hℓ α = prefixType G hℓ β ∨
      Disjoint (prefixType G hℓ α) (prefixType G hℓ β) := by
  obtain ⟨m, hm, _, hrow⟩ := common_support_and_row_maltsev L δ hAlg hBO
  exact complex_type_partition G hm (hrow n hn G hG) hℓ α β

end DegreeStructuralCollapse

open MaltsevRelations RowTypes
variable {D ι : Type} [Fintype D] (L : Language D ℂ ι) (δ : ℕ)

/-- Original proportional-row prefix types for all degree-generated tables. -/
def DegreeGlobalTypePartition : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n + 1) → D) → ℂ), DegreeGenerated L δ G →
    ∀ (ℓ : ℕ) (hℓ : ℓ ≤ n) (α β : Fin ℓ → D),
      prefixType G hℓ α = prefixType G hℓ β ∨
        Disjoint (prefixType G hℓ α) (prefixType G hℓ β)

/-- One common operation precedes all degree-generated support and Ω quantifiers. -/
def DegreeGlobalMaltsev : Prop :=
  ∃ m : Operation D, IsMaltsev m ∧
    (∀ T : PositiveTable D, DegreeGenerated L δ T.value →
      Preserves m {a | T.value a ≠ 0}) ∧
    ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n + 1) → D) → ℂ),
      DegreeGenerated L δ G → Preserves m (omegaRelation G).tuples

/-- The three Cai--Chen conditions with exactly the degree-restricted family. -/
def DegreeCaiChenConditions : Prop :=
  DegreeJointBO L δ ∧ DegreeGlobalTypePartition L δ ∧ DegreeGlobalMaltsev L δ

theorem DegreeJointBO.global_type_partition [Nonempty D] [Fintype ι]
    (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) (hBO : DegreeJointBO L δ) :
    DegreeGlobalTypePartition L δ := by
  intro n hn G hG ℓ hℓ α β
  exact DegreeStructuralCollapse.generated_type_partition L δ hAlg hBO hn G hG hℓ α β

theorem DegreeJointBO.global_maltsev [Nonempty D] [Fintype ι]
    (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) (hBO : DegreeJointBO L δ) :
    DegreeGlobalMaltsev L δ := by
  obtain ⟨m,hm,hsupp,hrow⟩ :=
    DegreeStructuralCollapse.common_support_and_row_maltsev L δ hAlg hBO
  refine ⟨m,hm,?_,hrow⟩
  intro T hT
  let R : Relation D := ⟨T.rowArity + 1,{a | T.value a ≠ 0}⟩
  exact hsupp R ⟨T.value,hT,rfl⟩

/-- The structural portion of Corollary 1.2, independent of the disputed
isomorphism theorem and without an unrestricted-BO assumption. The implication
is valid even at δ = 0; the paper requests the positive-δ cases. -/
theorem degree_structural_collapse [Nonempty D] [Fintype ι]
    (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    DegreeCaiChenConditions L δ ↔ DegreeJointBO L δ := by
  constructor
  · exact And.left
  · intro hBO
    exact ⟨hBO,hBO.global_type_partition L δ hAlg,hBO.global_maltsev L δ hAlg⟩

/-- The final Type Partition condition has exactly the ordered degree semantics. -/
theorem degreeGlobalTypePartition_iff_ordered : DegreeGlobalTypePartition L δ ↔
    ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n + 1) → D) → ℂ), PaperDegreeGenerated L δ G →
      ∀ (ℓ : ℕ) (hℓ : ℓ ≤ n) (α β : Fin ℓ → D),
        prefixType G hℓ α = prefixType G hℓ β ∨
          Disjoint (prefixType G hℓ α) (prefixType G hℓ β) := by
  simp only [DegreeGlobalTypePartition, degreeGenerated_iff_paperDegreeGenerated]

/-- The same single operation preserves every support and row relation in the
paper's ordered degree-divisible family. -/
theorem degreeGlobalMaltsev_iff_ordered : DegreeGlobalMaltsev L δ ↔
    ∃ m : Operation D, IsMaltsev m ∧
      (∀ T : PositiveTable D, PaperDegreeGenerated L δ T.value →
        Preserves m {a | T.value a ≠ 0}) ∧
      ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n + 1) → D) → ℂ),
        PaperDegreeGenerated L δ G → Preserves m (omegaRelation G).tuples := by
  simp only [DegreeGlobalMaltsev, degreeGenerated_iff_paperDegreeGenerated]

/-- Sanity check: the prefix-type condition specializes exactly at δ = 1. -/
theorem degreeGlobalTypePartition_one_iff :
    DegreeGlobalTypePartition L 1 ↔ GlobalTypePartition L := by
  simp only [DegreeGlobalTypePartition, GlobalTypePartition,
    DegreeGenerated.at_one_iff, generated_iff_paperGenerated]

/-- Sanity check: the common-operation quantifier specializes exactly at δ = 1. -/
theorem degreeGlobalMaltsev_one_iff : DegreeGlobalMaltsev L 1 ↔ GlobalMaltsev L := by
  simp only [DegreeGlobalMaltsev, GlobalMaltsev,
    DegreeGenerated.at_one_iff, generated_iff_paperGenerated]

/-- All three actual degree conditions reduce to the ordinary conditions at one. -/
theorem degreeCaiChenConditions_one_iff : DegreeCaiChenConditions L 1 ↔ CaiChenConditions L := by
  simp only [DegreeCaiChenConditions, CaiChenConditions, degreeJointBO_one_iff,
    degreeGlobalTypePartition_one_iff, degreeGlobalMaltsev_one_iff]

end ComplexCSP
