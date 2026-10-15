import ComplexCSP.Recognition.CertificatesEmbeddingLift

/-!
# Certificate roots from an arbitrary proved runtime exponent

The root alphabet uses `rootsOfUnity E K` for the supplied natural exponent E.
A positive E and a proved torsion-killing property suffice for completeness.
Finite enumeration is an explicit typeclass input to the finite-program
endpoints; this module does not install a noncomputable enumeration.
-/

namespace ComplexCSP.Certificates

variable {K : Type*} [Field K]

/-- Root values, one, and inverse/conjugation lookup for a runtime exponent. -/
def exponentRootAlphabet (K : Type*) [Field K] (E : ℕ) :
    RootAlphabet K (rootsOfUnity E K) where
  value := fun r ↦ (r.val : K)
  one := 1
  conj := Inv.inv
  value_one := rfl

theorem exponentRoot_finite_order (E : ℕ) (hE : 0 < E) (r : rootsOfUnity E K) :
    IsOfFinOrder ((exponentRootAlphabet K E).value r) :=
  isOfFinOrder_iff_pow_eq_one.mpr ⟨E, hE, (mem_rootsOfUnity' _ _).mp r.property⟩

theorem exponentRoots_complete (E : ℕ) (hkill : RowDetector.KillsTorsion K E)
    (x : K) (hx : IsOfFinOrder x) :
    ∃ r : rootsOfUnity E K, (exponentRootAlphabet K E).value r = x := by
  refine ⟨⟨hx.unit, (mem_rootsOfUnity' _ _).mpr (hkill x hx)⟩, rfl⟩

/-- Complex realization of the runtime-exponent root alphabet. -/
def exponentRootRealization (σ : K →+* ℂ) (E : ℕ) (hE : 0 < E) :
    ComplexRealization (exponentRootAlphabet K E) where
  hom := σ
  norm_root r := (σ.toMonoidHom.isOfFinOrder (exponentRoot_finite_order E hE r)).norm_eq_one
  conj_root r := by
    change σ (((r⁻¹ : rootsOfUnity E K).val : K)) = star (σ (r.val : K))
    simp only [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
    rw [map_inv₀, Complex.inv_def, Complex.normSq_eq_norm_sq]
    have hn : ‖σ (r.val : K)‖ = 1 :=
      (σ.toMonoidHom.isOfFinOrder (exponentRoot_finite_order E hE r)).norm_eq_one
    simp [hn]

/-- Local entry tests transport across two root alphabets with the same values.
This is used only with value coverage proved from actual root enumeration. -/
theorem IntrinsicTests.change_roots {X D R₁ R₂ : Type*}
    {roots₁ : RootAlphabet K R₁} {roots₂ : RootAlphabet K R₂}
    {realize₁ : ComplexRealization roots₁} {realize₂ : ComplexRealization roots₂}
    {A : X → D → K} {P : X → D → ℂ}
    (tests : IntrinsicTests roots₁ realize₁ A P)
    (hσ : realize₂.hom = realize₁.hom)
    (h₁₂ : ∀ r₁, ∃ r₂, roots₂.value r₂ = roots₁.value r₁)
    (h₂₁ : ∀ r₂, ∃ r₁, roots₁.value r₁ = roots₂.value r₂) :
    IntrinsicTests roots₂ realize₂ A P where
  zero := tests.zero
  ordinary_minor := tests.ordinary_minor
  magnitude_minor x y z w := by
    rw [tests.magnitude_minor]
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨s, hs⟩ := h₁₂ r
      exact ⟨s, by rw [hs]; exact hr⟩
    · rintro ⟨s, hs⟩
      obtain ⟨r, hr⟩ := h₂₁ s
      exact ⟨r, by rw [hr]; exact hs⟩
  root_covariance x z w s h := by
    obtain ⟨r, hr⟩ := h₂₁ s
    rw [hσ]
    have hh := tests.root_covariance x z w r (by rw [hr]; exact h)
    simpa only [hr] using hh
  magnitude_anchor x z w hw := by
    rw [tests.magnitude_anchor x z w hw]
    constructor
    · rintro ⟨r, hr⟩
      obtain ⟨s, hs⟩ := h₁₂ r
      exact ⟨s, by rw [hs]; exact hr⟩
    · rintro ⟨s, hs⟩
      obtain ⟨r, hr⟩ := h₂₁ s
      exact ⟨r, by rw [hr]; exact hs⟩

/-- The actual legal-table entry tests with a runtime torsion exponent. No
intrinsic-test or enumeration-completeness assumption is supplied. -/
theorem intrinsicTests_embedded_legalTable_exponent {X D : Type*} [NumberField K]
    (σ : K →+* ℂ) {S : Finset ℂˣ} (L : GeneratingSet.LegalGeneratingSet S)
    (A : X → D → K)
    (hA : GeneratingSet.LegalGeneratingSet.ContainsTable S (fun x z ↦ σ (A x z)))
    (E : ℕ) (hE : 0 < E) (hkill : RowDetector.KillsTorsion K E) :
    IntrinsicTests (exponentRootAlphabet K E) (exponentRootRealization σ E hE) A
      (L.purifyTable (fun x z ↦ σ (A x z)) hA) := by
  apply (intrinsicTests_embedded_legalTable σ L A hA).change_roots
    (roots₂ := exponentRootAlphabet K E) (realize₂ := exponentRootRealization σ E hE) rfl
  · intro r
    exact exponentRoots_complete E hkill _ (numberFieldRoot_finite_order r)
  · intro r
    exact numberFieldRoots_complete _ (exponentRoot_finite_order E hE r)

theorem embedded_legal_blockOrthogonal_iff_exponent_certificate {X D : Type*}
    [Fintype D] [DecidableEq D] [NumberField K]
    (σ : K →+* ℂ) {S : Finset ℂˣ} (L : GeneratingSet.LegalGeneratingSet S)
    (A : X → D → K)
    (hA : GeneratingSet.LegalGeneratingSet.ContainsTable S (fun x z ↦ σ (A x z)))
    (E : ℕ) (hE : 0 < E) (hkill : RowDetector.KillsTorsion K E) :
    BlockOrthogonality.BlockOrthogonal (L.purifyTable (fun x z ↦ σ (A x z)) hA) ↔
      ∃ c : Certificate X D (rootsOfUnity E K), c.Retained (exponentRootAlphabet K E) ∧
        Satisfies (exponentRootAlphabet K E) c A :=
  blockOrthogonal_iff_certificate (intrinsicTests_embedded_legalTable_exponent σ L A hA E hE hkill)

/-- The finite product-equation endpoint uses the caller's actual finite root
enumeration, allowing the raw-coefficient algorithm to supply it. -/
theorem embedded_legal_blockOrthogonal_iff_exponent_products {X D : Type*}
    [Fintype X] [DecidableEq X] [Fintype D] [DecidableEq D]
    [NumberField K] [DecidableEq K]
    (σ : K →+* ℂ) {S : Finset ℂˣ} (L : GeneratingSet.LegalGeneratingSet S)
    (A : X → D → K)
    (hA : GeneratingSet.LegalGeneratingSet.ContainsTable S (fun x z ↦ σ (A x z)))
    (E : ℕ) [Fintype (rootsOfUnity E K)]
    (hE : 0 < E) (hkill : RowDetector.KillsTorsion K E) :
    BlockOrthogonality.BlockOrthogonal (L.purifyTable (fun x z ↦ σ (A x z)) hA) ↔
      ∀ q ∈ boProductEquations (X := X) (D := D) (exponentRootAlphabet K E),
        MvPolynomial.eval (fun p : X × D ↦ A p.1 p.2) q = 0 :=
  blockOrthogonal_iff_product_equations _ _ _ _
    (intrinsicTests_embedded_legalTable_exponent σ L A hA E hE hkill)

end ComplexCSP.Certificates
