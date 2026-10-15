import Paper2.HeightOne.GroupSplit.ActualTransfers
import Paper2.HeightOne.GroupSplit.DiagonalTransport
import Paper2.HeightOne.GroupSplit.Normalization

/-! Complete all-realizable projective transfer sets and their exact transport. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.GroupSplit
open MatrixGroup Tractable
noncomputable section

def actualClasses (F : SignatureFamily AlgebraicComplex) : Set (PGL2 AlgebraicComplex) :=
  {q | ∃ U : Matrix.GeneralLinearGroup Bool AlgebraicComplex,
    (U : AMat) ∈ actualTransfers F ∧ pglMk _ U = q}

lemma actualClasses_subgroup {F : SignatureFamily AlgebraicComplex}
    (hG : ProjectiveMatrixGroup (actualTransfers F)) :
    actualClasses F = (projectiveSubgroup hG : Set (PGL2 AlgebraicComplex)) := rfl

lemma binary_action_matrix (D : InvertibleKernel) (B : AMat) :
    D.action (binarySignature B) =
      binarySignature ((Matrix.of D.matrix) * B * (Matrix.of D.matrix).transpose) := by
  exact coordinateAction_kernelSignature D.matrix B

lemma conformal_transfer (D : InvertibleKernel) (c : AlgebraicComplex)
    (hD : Kernel.pullback Signature.disequality D.matrix =
      fun i j => c * Signature.disequality i j) (B : AMat) :
    transfer ((Matrix.of D.matrix) * B * (Matrix.of D.matrix).transpose) =
      c • ((Matrix.of D.matrix) * transfer B * (Matrix.of D.inverse)) := by
  have hp : (Matrix.of D.matrix).transpose * X * (Matrix.of D.matrix) = c • X := hD
  have hi : (Matrix.of D.matrix) * (Matrix.of D.inverse) = 1 := (basisGL D).val_inv
  have hright : (Matrix.of D.matrix).transpose * X = c • (X * (Matrix.of D.inverse)) := by
    have h := congrArg (fun M : AMat => M * (Matrix.of D.inverse)) hp
    simpa only [Matrix.mul_assoc, hi, Matrix.mul_one, Matrix.smul_mul] using h
  unfold transfer
  rw [Matrix.mul_assoc, Matrix.mul_assoc, hright, Matrix.mul_smul, Matrix.mul_smul]
  simp only [Matrix.mul_assoc]

lemma ActualNonsingular.diagonal_transport {F : SignatureFamily AlgebraicComplex}
    {B : AMat} (hB : ActualNonsingular F B)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpull : Kernel.pullback Signature.disequality D.matrix =
      fun i j => (a * b) * Signature.disequality i j) :
    ∃ B' : AMat, ActualNonsingular (familyAction D F) B' ∧
      ∃ c : AlgebraicComplex, c ≠ 0 ∧
        transfer B' = c • ((Matrix.of D.matrix) * transfer B * (Matrix.of D.inverse)) := by
  obtain ⟨c, hc, hreal⟩ := realizable_diagonal_transport hB.1 D a b hD ha hb
  let B' : AMat := c • ((Matrix.of D.matrix) * B * (Matrix.of D.matrix).transpose)
  have hreal' : NetworkRealizable (familyAction D F) (binarySignature B') := by
    rw [binary_action_matrix] at hreal
    exact hreal
  have hdetD : Matrix.det (Matrix.of D.matrix) ≠ 0 := Matrix.GeneralLinearGroup.det_ne_zero (basisGL D)
  refine ⟨B', ⟨hreal', ?_⟩, c * (a * b), mul_ne_zero hc (mul_ne_zero ha hb), ?_⟩
  · dsimp [B']
    rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hc) (mul_ne_zero (mul_ne_zero hdetD hB.2) hdetD)
  · dsimp [B']
    rw [transfer, Matrix.smul_mul]
    change c • transfer ((Matrix.of D.matrix) * B * (Matrix.of D.matrix).transpose) = _
    rw [conformal_transfer D (a * b) hpull, smul_smul]

lemma actualClasses_transport_forward {F : SignatureFamily AlgebraicComplex}
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (hpull : Kernel.pullback Signature.disequality D.matrix =
      fun i j => (a * b) * Signature.disequality i j)
    {q : PGL2 AlgebraicComplex} (hq : q ∈ actualClasses F) :
    pglMk _ (basisGL D) * q * (pglMk _ (basisGL D))⁻¹ ∈ actualClasses (familyAction D F) := by
  obtain ⟨U, ⟨B, hB, t, ht, hU⟩, rfl⟩ := hq
  obtain ⟨B', hB', c, hc, he⟩ := hB.diagonal_transport D a b hD ha hb hpull
  let V := basisGL D * U * (basisGL D)⁻¹
  refine ⟨V, ⟨B', hB', t / c, div_ne_zero ht hc, ?_⟩, ?_⟩
  · change (Matrix.of D.matrix) * (U : AMat) * (Matrix.of D.inverse) = (t / c) • transfer B'
    rw [hU, Matrix.mul_smul, Matrix.smul_mul, he, smul_smul]
    rw [div_mul_cancel₀ _ hc]
  · simp only [V, map_mul, map_inv]


lemma inverse_diagonal (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    D.inverse = diagonalKernel a⁻¹ b⁻¹ := by
  let E := HeightTwo.diagonalBasis a b ha hb
  have he : Kernel.mul D.matrix E.inverse = Signature.equality := by
    rw [hD]
    exact E.matrix_inverse
  calc
    D.inverse = Kernel.mul D.inverse (Kernel.mul D.matrix E.inverse) := by
      rw [he, Kernel.mul_equality]
    _ = E.inverse := by rw [← Kernel.mul_assoc, D.inverse_matrix, Kernel.equality_mul]

@[simp] lemma basisGL_symm (D : InvertibleKernel) : basisGL D.symm = (basisGL D)⁻¹ :=
  Units.ext rfl

/-- Equality of the complete transfer sets, established in both directions by
actual graph transport. Every class in the image still has an actual witness. -/
theorem completeClasses_diagonal_transport (F : SignatureFamily AlgebraicComplex)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    actualClasses (familyAction D F) =
      (fun q => pglMk _ (basisGL D) * q * (pglMk _ (basisGL D))⁻¹) '' actualClasses F := by
  have hpull : Kernel.pullback Signature.disequality D.matrix =
      fun i j => (a * b) * Signature.disequality i j := by
    rw [hD]
    exact HeightTwo.diagonalBasis_pullback a b ha hb
  have hDi : D.symm.matrix = diagonalKernel a⁻¹ b⁻¹ := inverse_diagonal D a b hD ha hb
  have hpulli : Kernel.pullback Signature.disequality D.symm.matrix =
      fun i j => (a⁻¹ * b⁻¹) * Signature.disequality i j := by
    rw [hDi]
    exact HeightTwo.diagonalBasis_pullback a⁻¹ b⁻¹ (inv_ne_zero ha) (inv_ne_zero hb)
  ext q
  constructor
  · intro hq
    have hp := actualClasses_transport_forward D.symm a⁻¹ b⁻¹ hDi
      (inv_ne_zero ha) (inv_ne_zero hb) hpulli hq
    have hp' : (pglMk _ (basisGL D))⁻¹ * q * pglMk _ (basisGL D) ∈ actualClasses F := by
      simpa only [basisGL_symm, map_inv, inv_inv, Conformal.familyAction_symm_action] using hp
    refine ⟨_, hp', ?_⟩
    group
  · rintro ⟨q, hq, rfl⟩
    exact actualClasses_transport_forward D a b hD ha hb hpull hq


lemma binarySignature_ne_zero {B : AMat} (hB : B ≠ 0) : binarySignature B ≠ 0 := by
  intro h
  apply hB
  funext i j
  exact congrFun h ![i, j]

/-- A legal diagonal normalization cannot create a nonzero singular actual
binary: inverse graph transport would give one in the original family. -/
theorem nonsingular_after_diagonal (F : SignatureFamily AlgebraicComplex)
    (hsafe : ∀ B : AMat, NetworkRealizable F (binarySignature B) → B ≠ 0 → Matrix.det B ≠ 0)
    (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (B : AMat) (hB : NetworkRealizable (familyAction D F) (binarySignature B)) (hBne : B ≠ 0) :
    Matrix.det B ≠ 0 := by
  have hDi : D.symm.matrix = diagonalKernel a⁻¹ b⁻¹ := inverse_diagonal D a b hD ha hb
  obtain ⟨c, hc, hreal⟩ := realizable_diagonal_transport hB D.symm a⁻¹ b⁻¹ hDi
    (inv_ne_zero ha) (inv_ne_zero hb)
  rw [Conformal.familyAction_symm_action] at hreal
  let C : AMat := c • (Matrix.of D.inverse * B * (Matrix.of D.inverse).transpose)
  have hCeq : binarySignature C = c • D.symm.action (binarySignature B) := by
    rw [binary_action_matrix]
    rfl
  have hCr : NetworkRealizable F (binarySignature C) := hCeq.symm ▸ hreal
  have hCne : C ≠ 0 := by
    intro hz
    have hzero : c • D.symm.action (binarySignature B) = 0 := by rw [← hCeq, hz]; rfl
    have hactzero : D.symm.action (binarySignature B) = 0 := by
      funext x
      exact (mul_eq_zero.mp (congrFun hzero x)).resolve_left hc
    have hzsig : binarySignature B = 0 := by
      have hh := congrArg D.action hactzero
      rw [D.action_symm_action] at hh
      simpa only [InvertibleKernel.action, Signature.coordinateAction_zero] using hh
    exact binarySignature_ne_zero hBne hzsig
  have hCdet := hsafe C hCr hCne
  intro hdet
  apply hCdet
  dsimp [C]
  rw [Matrix.det_smul, Matrix.det_mul, Matrix.det_mul, hdet]
  simp

end
end Paper2.HeightOne.GroupSplit
