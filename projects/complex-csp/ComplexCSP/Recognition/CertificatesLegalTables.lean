import ComplexCSP.Recognition.CertificatesFieldLift
import ComplexCSP.Algebra.LegalPurificationTables

/-!
# Finite certificate loci for actual legal purifications of number-field tables

The final statements take an actual field-valued table and any genuine legal
ambient generating choice. The intrinsic group, zero encoding, finite root
alphabet, and every local purification test are constructed, not assumed.
The computational representation of arbitrary algebraic number fields remains
separate from these mathematical finite-locus theorems.
-/

namespace ComplexCSP.Certificates

open Purification
open Purification.PurificationMap
open GeneratingSet

/-- The intrinsic group of a table stays in every subfield containing its entries. -/
theorem table_entryGroup_le_unitsInSubfield {X D : Type*}
    (K : Subfield ℂ) (G : X → D → ℂ) (hG : ∀ x z, G x z ∈ K) :
    entryGroup G ≤ unitsInSubfield K := by
  apply (Subgroup.closure_le _).mpr
  rintro u ⟨x, z, h⟩
  change (u : ℂ) ∈ K
  rw [h]
  exact hG x z

/-- The source-field interpretation of the canonical option encoding is exactly
the original table value, including zero entries. -/
theorem fieldEntry_encodeTable {X D : Type*} (K : Subfield ℂ)
    (G : X → D → ℂ) (hG : ∀ x z, G x z ∈ K) (x : X) (z : D) :
    fieldEntry (groupLift K (entryGroup G) (table_entryGroup_le_unitsInSubfield K G hG))
      (encodeTable G x z) = (⟨G x z, hG x z⟩ : K) := by
  classical
  apply Subtype.ext
  by_cases hz : G x z = 0
  · simp [encodeTable, hz]
  · simp [encodeTable, hz, fieldValueHom, groupLift]

/-- Every intrinsic test for an actual field-valued table and any legal ambient
purification is a theorem, rather than a supplied interface assumption. -/
theorem intrinsicTests_legalTable {X D : Type*} (K : Subfield ℂ) [NumberField K]
    {S : Finset ℂˣ} (L : LegalGeneratingSet S) (A : X → D → K)
    (hA : LegalGeneratingSet.ContainsTable S (fun x z ↦ (A x z : ℂ))) :
    IntrinsicTests (numberFieldRootAlphabet K) (numberFieldRootRealization K.subtype) A
      (L.purifyTable (fun x z ↦ (A x z : ℂ)) hA) := by
  let G : X → D → ℂ := fun x z ↦ A x z
  let hG : ∀ x z, G x z ∈ K := fun x z ↦ (A x z).property
  have tests := intrinsicTests_subfield K (entryGroup G)
    (table_entryGroup_le_unitsInSubfield K G hG) (L.tableMap G hA) (encodeTable G)
  have hfield : (fun x z ↦ fieldEntry
      (groupLift K (entryGroup G) (table_entryGroup_le_unitsInSubfield K G hG))
      (encodeTable G x z)) = A := by
    funext x z
    exact fieldEntry_encodeTable K G hG x z
  rw [hfield] at tests
  exact tests

/-- Theorem 4.2's finite-certificate equivalence for actual number-field tables
and actual arbitrary legal choices. No assumed intrinsic tests remain. -/
theorem legal_purified_blockOrthogonal_iff_certificate {X D : Type*}
    [Fintype D] [DecidableEq D] (K : Subfield ℂ) [NumberField K]
    {S : Finset ℂˣ} (L : LegalGeneratingSet S) (A : X → D → K)
    (hA : LegalGeneratingSet.ContainsTable S (fun x z ↦ (A x z : ℂ))) :
    BlockOrthogonality.BlockOrthogonal (L.purifyTable (fun x z ↦ (A x z : ℂ)) hA) ↔
      ∃ c : Certificate X D (NumberFieldRoots K),
        c.Retained (numberFieldRootAlphabet K) ∧ Satisfies (numberFieldRootAlphabet K) c A :=
  blockOrthogonal_iff_certificate (intrinsicTests_legalTable K L A hA)

/-- The actual finite union of polynomial zero loci, uniformly in the table
and independent of the legal ambient choice. -/
theorem legal_purified_blockOrthogonal_iff_finite_union {X D : Type*}
    [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]
    (K : Subfield ℂ) [NumberField K] [DecidableEq K]
    {S : Finset ℂˣ} (L : LegalGeneratingSet S) (A : X → D → K)
    (hA : LegalGeneratingSet.ContainsTable S (fun x z ↦ (A x z : ℂ))) :
    BlockOrthogonality.BlockOrthogonal (L.purifyTable (fun x z ↦ (A x z : ℂ)) hA) ↔
      ∃ c : RetainedCertificate (X := X) (D := D) (numberFieldRootAlphabet K),
        (fun p : X × D ↦ A p.1 p.2) ∈
          ComplexCSP.polynomialZeroLocus (equationSet (numberFieldRootAlphabet K) c.val) :=
  blockOrthogonal_iff_finite_union _ _ _ _ (intrinsicTests_legalTable K L A hA)

/-- Corollary 4.4 for the actual, constructed legal-purification locus. -/
theorem legal_purified_blockOrthogonal_iff_product_equations {X D : Type*}
    [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]
    (K : Subfield ℂ) [NumberField K] [DecidableEq K]
    {S : Finset ℂˣ} (L : LegalGeneratingSet S) (A : X → D → K)
    (hA : LegalGeneratingSet.ContainsTable S (fun x z ↦ (A x z : ℂ))) :
    BlockOrthogonality.BlockOrthogonal (L.purifyTable (fun x z ↦ (A x z : ℂ)) hA) ↔
      ∀ q ∈ boProductEquations (X := X) (D := D) (numberFieldRootAlphabet K),
        MvPolynomial.eval (fun p : X × D ↦ A p.1 p.2) q = 0 :=
  blockOrthogonal_iff_product_equations _ _ _ _ (intrinsicTests_legalTable K L A hA)

/-- Positive denominator clearing does not alter the same finite certificate
locus. This covers the pure-integer-magnitude legal output convention. -/
theorem normalized_legal_blockOrthogonal_iff_certificate {X D : Type*}
    [Fintype D] [DecidableEq D] (K : Subfield ℂ) [NumberField K]
    {S : Finset ℂˣ} (L : LegalGeneratingSet S) (A : X → D → K)
    (hA : LegalGeneratingSet.ContainsTable S (fun x z ↦ (A x z : ℂ)))
    (N : ℝ) (hN : 0 < N) :
    BlockOrthogonality.BlockOrthogonal
        (fun x z ↦ (N : ℂ) * L.purifyTable (fun x z ↦ (A x z : ℂ)) hA x z) ↔
      ∃ c : Certificate X D (NumberFieldRoots K),
        c.Retained (numberFieldRootAlphabet K) ∧ Satisfies (numberFieldRootAlphabet K) c A := by
  rw [BlockOrthogonality.blockOrthogonal_positive_scale_iff hN]
  exact legal_purified_blockOrthogonal_iff_certificate K L A hA

end ComplexCSP.Certificates
