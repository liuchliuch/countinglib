import ComplexCSP.Recognition.CertificatesLegalTables

/-!
# Actual certificate loci under a generic number-field embedding

The source field remains an arbitrary executable field representation. Complex
subfields occur nowhere in the public endpoint. The noncomputable group lift
is confined to proof-level purification semantics.
-/

namespace ComplexCSP.Certificates

open Purification
open Purification.PurificationMap
open GeneratingSet

variable {K : Type*} [Field K]

def unitEmbedding (σ : K →+* ℂ) : Kˣ →* ℂˣ := Units.map σ.toMonoidHom

theorem unitEmbedding_injective (σ : K →+* ℂ) : Function.Injective (unitEmbedding σ) :=
  Units.map_injective σ.injective

noncomputable def embeddingGroupLift (σ : K →+* ℂ) (Γ : Subgroup ℂˣ)
    (hΓ : Γ ≤ (unitEmbedding σ).range) : Γ →* Kˣ :=
  (MonoidHom.ofInjective (unitEmbedding_injective σ)).symm.toMonoidHom.comp
    (Subgroup.inclusion hΓ)

@[simp] theorem unitEmbedding_embeddingGroupLift (σ : K →+* ℂ) (Γ : Subgroup ℂˣ)
    (hΓ : Γ ≤ (unitEmbedding σ).range) (x : Γ) :
    unitEmbedding σ (embeddingGroupLift σ Γ hΓ x) = x.val := by
  have h := (MonoidHom.ofInjective (unitEmbedding_injective σ)).apply_symm_apply
    (Subgroup.inclusion hΓ x)
  exact congrArg Subtype.val h

theorem embeddingGroupLift_injective (σ : K →+* ℂ) (Γ : Subgroup ℂˣ)
    (hΓ : Γ ≤ (unitEmbedding σ).range) : Function.Injective (embeddingGroupLift σ Γ hΓ) := by
  intro x y h
  have hh := congrArg (unitEmbedding σ) h
  rw [unitEmbedding_embeddingGroupLift, unitEmbedding_embeddingGroupLift] at hh
  exact Subtype.ext hh

@[simp] theorem complexOriginal_embeddingGroupLift (σ : K →+* ℂ) (Γ : Subgroup ℂˣ)
    (hΓ : Γ ≤ (unitEmbedding σ).range) :
    complexOriginal σ (embeddingGroupLift σ Γ hΓ) = Γ.subtype := by
  apply MonoidHom.ext
  exact unitEmbedding_embeddingGroupLift σ Γ hΓ

/-- The original table's intrinsic group is contained in the embedding's unit
range, since each generator is an actually embedded field element. -/
theorem entryGroup_le_embeddingRange {X D : Type*} (σ : K →+* ℂ) (A : X → D → K) :
    entryGroup (fun x z ↦ σ (A x z)) ≤ (unitEmbedding σ).range := by
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨x, z, hu⟩
  have ha : A x z ≠ 0 := by
    intro hz
    apply Units.ne_zero u
    calc
      (u : ℂ) = σ (A x z) := hu
      _ = 0 := by rw [hz, map_zero]
  refine ⟨Units.mk0 (A x z) ha, ?_⟩
  apply Units.ext
  exact hu.symm

noncomputable def embeddedPurificationMap (σ : K →+* ℂ) (Γ : Subgroup ℂˣ)
    (hΓ : Γ ≤ (unitEmbedding σ).range) (P : PurificationMap Γ Γ.subtype) :
    PurificationMap Γ (complexOriginal σ (embeddingGroupLift σ Γ hΓ)) where
  hom := P.hom
  injective := P.injective
  fixes_torsion x hx := by
    rw [complexOriginal_embeddingGroupLift]
    exact P.fixes_torsion x hx
  norm_one_iff := P.norm_one_iff

/-- Pulling the canonical actual-table encoding back through the embedding gives
exactly the original executable-field table. -/
theorem embedded_fieldEntry_encodeTable {X D : Type*} (σ : K →+* ℂ)
    (A : X → D → K) (x : X) (z : D) :
    fieldEntry (embeddingGroupLift σ (entryGroup (fun x z ↦ σ (A x z)))
      (entryGroup_le_embeddingRange σ A)) (encodeTable (fun x z ↦ σ (A x z)) x z) = A x z := by
  classical
  apply σ.injective
  by_cases ha : A x z = 0
  · simp [encodeTable, ha]
  · have hσ : σ (A x z) ≠ 0 := fun hz ↦ ha (σ.injective (hz.trans σ.map_zero.symm))
    simp only [encodeTable, dif_neg hσ, fieldEntry_some, fieldValueHom_apply]
    change (unitEmbedding σ (embeddingGroupLift σ _ _ _ ) : ℂ) = σ (A x z)
    rw [unitEmbedding_embeddingGroupLift]
    rfl

/-- All intrinsic tests are derived for an actual table over a generic number
field and its genuine legal complex purification. -/
theorem intrinsicTests_embedded_legalTable {X D : Type*} [NumberField K]
    (σ : K →+* ℂ) {S : Finset ℂˣ} (L : LegalGeneratingSet S) (A : X → D → K)
    (hA : LegalGeneratingSet.ContainsTable S (fun x z ↦ σ (A x z))) :
    IntrinsicTests (numberFieldRootAlphabet K) (numberFieldRootRealization σ) A
      (L.purifyTable (fun x z ↦ σ (A x z)) hA) := by
  let G := fun x z ↦ σ (A x z)
  let Γ := entryGroup G
  let hΓ := entryGroup_le_embeddingRange σ A
  let ρ := embeddingGroupLift σ Γ hΓ
  let P := L.tableMap G hA
  have tests := intrinsicTests_of_purificationMap σ ρ
    (embeddingGroupLift_injective σ Γ hΓ) (embeddedPurificationMap σ Γ hΓ P) (encodeTable G)
  have hfield : (fun x z ↦ fieldEntry ρ (encodeTable G x z)) = A := by
    funext x z
    exact embedded_fieldEntry_encodeTable σ A x z
  rw [hfield] at tests
  exact tests

/-- Certificate soundness and completeness over the generic source field,
without executing any complex-subfield conversion. -/
theorem embedded_legal_blockOrthogonal_iff_certificate {X D : Type*}
    [Fintype D] [DecidableEq D] [NumberField K]
    (σ : K →+* ℂ) {S : Finset ℂˣ} (L : LegalGeneratingSet S) (A : X → D → K)
    (hA : LegalGeneratingSet.ContainsTable S (fun x z ↦ σ (A x z))) :
    BlockOrthogonality.BlockOrthogonal (L.purifyTable (fun x z ↦ σ (A x z)) hA) ↔
      ∃ c : Certificate X D (NumberFieldRoots K), c.Retained (numberFieldRootAlphabet K) ∧
        Satisfies (numberFieldRootAlphabet K) c A :=
  blockOrthogonal_iff_certificate (intrinsicTests_embedded_legalTable σ L A hA)

/-- Product identities for actual generic-field input tables and their legal
complex purification, with every semantic bridge derived. -/
theorem embedded_legal_blockOrthogonal_iff_product_equations {X D : Type*}
    [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]
    [NumberField K] [DecidableEq K]
    (σ : K →+* ℂ) {S : Finset ℂˣ} (L : LegalGeneratingSet S) (A : X → D → K)
    (hA : LegalGeneratingSet.ContainsTable S (fun x z ↦ σ (A x z))) :
    BlockOrthogonality.BlockOrthogonal (L.purifyTable (fun x z ↦ σ (A x z)) hA) ↔
      ∀ q ∈ boProductEquations (X := X) (D := D) (numberFieldRootAlphabet K),
        MvPolynomial.eval (fun p : X × D ↦ A p.1 p.2) q = 0 :=
  blockOrthogonal_iff_product_equations _ _ _ _ (intrinsicTests_embedded_legalTable σ L A hA)

end ComplexCSP.Certificates
