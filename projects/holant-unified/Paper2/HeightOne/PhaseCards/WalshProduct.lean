import Paper2.HeightOne.PhaseCards.ProductPresentation
import Paper2.HeightOne.PhaseCards.FactorSaturation
import Paper2.HeightOne.PhaseCards.Source
import Paper2.Tractable.Conformal

/-! A single concrete Walsh basis for the entire saturated language, with the
edge explicitly in Product as well. This is the common presentation used at
the end of both odd-group branches. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable GroupSplit GroupSplit.MatrixGroup
open GroupSplit.FiniteGroupFacts.ProjectiveCentralizers

/-- The analytic Walsh matrix with its actual certified inverse. -/
def walshBasis : InvertibleKernel where
  matrix := walsh
  inverse := walshInv
  matrix_inverse := walsh_mul_walshInv
  inverse_matrix := walshInv_mul_walsh

lemma walshBasis_inverse_action {n : ℕ} (f : Signature AlgebraicComplex n) :
    walshBasis.symm.action f = walshCoordinates f :=
  (walshCoordinates_eq_coordinateAction f).symm

lemma diagonal_binary_product (B : AMat) (h01 : B false true = 0) (h10 : B true false = 0) :
    Product (binarySignature B) := by
  have h := (product_unary (0 : Fin 2) (fun b => B b b)).mul (product_equality 0 1)
  convert h using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [binarySignature, Signature.equality, h0, h1, h01, h10]

lemma antidiagonal_binary_product (B : AMat) (h00 : B false false = 0) (h11 : B true true = 0) :
    Product (binarySignature B) := by
  have h := (product_unary (0 : Fin 2) (fun b => B b (!b))).mul (product_disequality 0 1)
  convert h using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [binarySignature, Signature.disequality, h0, h1, h00, h11]

/-- The native edge has the standard Product normal form under the very same P. -/
theorem walsh_edge_product :
    Product (kernelSignature (Kernel.pullback Signature.disequality walshBasis.matrix)) := by
  have he : Kernel.pullback Signature.disequality walshBasis.matrix =
      (2 : AlgebraicComplex) • (zGL : AMat) := walsh_native_edge
  rw [he]
  apply diagonal_binary_product <;>
    simp [zGL, diagonalGL, diagonal]

/-- The entire family and its edge use one witness `K P` in original coordinates. -/
theorem common_product_transform_of_walsh
    (F : SignatureFamily AlgebraicComplex) (hfinite : F.Finite)
    (hF : ∀ f ∈ F, Product (walshCoordinates f.2)) :
    CommonTransformable productClass (familyAction sourceKBasis F) := by
  refine ⟨hfinite.image _, sourceKBasis.comp walshBasis, ?_, ?_⟩
  · change Product (kernelSignature (Kernel.pullback Signature.equality
      (Kernel.mul sourceKBasis.matrix walshBasis.matrix)))
    rw [pullback_mul, sourceKBasis_pullback]
    exact walsh_edge_product
  · rintro f ⟨g, hg, rfl⟩
    change Product ((sourceKBasis.comp walshBasis).symm.action (sourceKBasis.action g.2))
    rw [InvertibleKernel.comp_symm, InvertibleKernel.comp_action,
      InvertibleKernel.symm_action_action, walshBasis_inverse_action]
    exact hF g hg

theorem common_product_transform_of_phaseProducts
    (F : SignatureFamily AlgebraicComplex) (hfinite : F.Finite) (N : ℕ)
    (hF : ∀ f ∈ F, PhaseProduct N (walshCoordinates f.2)) :
    CommonTransformable productClass (familyAction sourceKBasis F) :=
  common_product_transform_of_walsh F hfinite (fun f hf => (hF f hf).product)

/-- Complete normalized group membership gives a genuine Product normal form
for each actual nonsingular binary, without varying the Walsh basis. -/
theorem normalized_binary_product {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N ∨ actualClasses F = dihedralPhaseClasses N)
    {B : AMat} (hB : ActualNonsingular F B) : Product (walshCoordinates (binarySignature B)) := by
  rcases actual_binary_phase_shape hG hB with ⟨s, c, hc, h⟩ | ⟨s, c, hc, h⟩
  · rw [walshCoordinates_binary, rotation_walsh_binary h]
    apply diagonal_binary_product <;> simp [plusKernel]
  · rw [walshCoordinates_binary, reflection_walsh_binary h]
    apply antidiagonal_binary_product <;> simp [reflectedBinary]

lemma normalized_signature_product {F : SignatureFamily AlgebraicComplex} {N n : ℕ}
    (hG : actualClasses F = cyclicPhaseClasses N ∨ actualClasses F = dihedralPhaseClasses N)
    (hsafe : AllBinariesSafe F) (f : Signature AlgebraicComplex n) (hn : n = 2)
    (hr : NetworkRealizable F f) (hp : f ≠ 0) : Product (walshCoordinates f) := by
  subst n
  have h := normalized_binary_product hG (actual_tableBinary hsafe f hr hp)
  rwa [binarySignature_tableBinary] at h

/-- The no-nonbinary-prime end of either odd-group branch supplies the literal
whole-family common product presentation, including higher-arity composites. -/
theorem common_product_transform_of_binary_primes
    (F : SignatureFamily AlgebraicComplex) (hfinite : F.Finite) (hfac : FactorClosed F)
    (hsafe : AllBinariesSafe F) (N : ℕ)
    (hG : actualClasses F = cyclicPhaseClasses N ∨ actualClasses F = dihedralPhaseClasses N)
    (hbinary : ∀ f ∈ F, TensorPrime f.2 → f.1 = 2) :
    CommonTransformable productClass (familyAction sourceKBasis F) := by
  apply common_product_transform_of_walsh F hfinite
  intro f hf
  obtain ⟨D, hD, hpos, hprime, hmem⟩ := hfac f hf
  have hfactor : ∀ i, Product (walshCoordinates (D.factor i)) := by
    intro i
    have hn := hbinary ⟨D.arity i, D.factor i⟩ (hmem i) (hprime i)
    exact normalized_signature_product hG hsafe (D.factor i) hn
      (networkRealizable_of_mem (hmem i)) (hprime i).1
  have hvalue := Product.decomposition (D.mapAction walshInv) (fun i => by
    simpa only [TensorDecomposition.mapAction, ← walshCoordinates_eq_coordinateAction] using hfactor i)
  have he := (TensorDecomposition.value_mapAction D walshInv).trans
    (walshCoordinates_eq_coordinateAction D.value).symm
  rw [he, hD] at hvalue
  exact hvalue

end
end Paper2.HeightOne.PhaseCards
