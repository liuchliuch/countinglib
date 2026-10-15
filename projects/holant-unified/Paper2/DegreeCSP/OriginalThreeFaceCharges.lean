import Paper2.DegreeCSP.OriginalThreeFaceContext
import Paper2.DegreeCSP.SignedCubeNormalizer

/-! Signed cancellation of the actual boundary degrees of eight original
three-face presentations. No affinity or generated-substitution premise is
used in this finite charge calculation. -/
namespace Paper2.DegreeCSP.OriginalThreeFaceCharges
open scoped BigOperators
open OriginalThreeFaceContext
open Holant.Tractable.AffinePhase (Word origin basis)
noncomputable section
set_option maxHeartbeats 1600000

variable {n k : ℕ}

/-- The actual context boundary degree, reduced modulo k. -/
def boundaryCharge (p : Word 3 → Word n) (k : ℕ) (j : Fin 7) : ZMod k :=
  (MultiCoordinateContext.boundaryWeight (AffineThreeFaceDecoder.decoder p) (k-1) j : ℕ)

/-- One literal original port's signed contribution. -/
def portCharge (e : MultiCoordinateContext.Expr 7) (j : Fin 7) : ℤ :=
  if e = Sum.inr (j,false) then 1 else if e = Sum.inr (j,true) then -1 else 0

theorem cast_pred (hk : 0 < k) : ((k-1 : ℕ) : ZMod k) = -1 := by
  have he : k-1+1=k := Nat.sub_add_cancel hk
  have h := congrArg (fun a : ℕ => (a : ZMod k)) he
  simp only [Nat.cast_add, Nat.cast_one, ZMod.natCast_self] at h
  exact eq_neg_iff_add_eq_zero.mpr h

/-- Degree k-1 on a complemented boundary is its genuine negative charge. -/
theorem boundaryCharge_eq_sum (hk : 0 < k) (p : Word 3 → Word n) (j : Fin 7) :
    boundaryCharge p k j = ∑ i, (portCharge (AffineThreeFaceDecoder.decoder p i) j : ZMod k) := by
  unfold boundaryCharge MultiCoordinateContext.boundaryWeight portCharge
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero,
    cast_pred hk, Int.cast_ite, Int.cast_one, Int.cast_neg, Int.cast_zero]

/-- The charge is literally the residue of the actual presentation degree. -/
theorem boundaryCharge_degree (p : Word 3 → Word n)
    (f : Signature Tractable.AlgebraicComplex n) (k : ℕ) (j : Fin 7) :
    boundaryCharge p k j = ((presentation p f k).degree (Sum.inl j) : ZMod k) := by
  rw [OriginalThreeFaceContext.boundary_degree]
  rfl

private def coefficientMask (b c₀ c₁ c₂ : Bool) : SignedCubeNormalizer.Mask :=
  ![Bool.xor c₀ b, Bool.xor c₁ b, Bool.xor c₂ b]

private theorem expression_charge (b c₀ c₁ c₂ : Bool) (j : Fin 7) :
    portCharge (AffineThreeFaceDecoder.expression b c₀ c₁ c₂) j =
      (if b then (-1 : ℤ) else 1) *
        (if coefficientMask b c₀ c₁ c₂ = SignedCubeNormalizer.bundleMask j then 1 else 0) := by
  cases b <;> cases c₀ <;> cases c₁ <;> cases c₂ <;> fin_cases j
  all_goals norm_num [portCharge, AffineThreeFaceDecoder.expression, coefficientMask,
    SignedCubeNormalizer.bundleMask, funext_iff, Fin.forall_fin_succ]

private theorem masked_coefficients (b c₀ c₁ c₂ : Bool) (u : Word 3) :
    coefficientMask b (if u 0 then c₀ else b) (if u 1 then c₁ else b)
      (if u 2 then c₂ else b) =
        SignedCubeNormalizer.intersection (coefficientMask b c₀ c₁ c₂) u := by
  have he (c t : Bool) : Bool.xor (if t then c else b) b = ((Bool.xor c b) && t) := by
    cases b <;> cases c <;> cases t <;> rfl
  funext i
  fin_cases i
  · exact he c₀ (u 0)
  · exact he c₁ (u 1)
  · exact he c₂ (u 2)

private theorem zeroFace_basis (u : Word 3) (j : Fin 3) :
    zeroFace u (basis j) = if u j then basis j else origin 3 := by
  funext i
  by_cases hij : i = j
  · subst i
    cases h : u j <;> simp [zeroFace, basis, origin, h]
  · cases u j <;> simp [zeroFace, basis, origin, hij]

theorem face_decoder (p : Word 3 → Word n) (u : Word 3) (i : Fin n) :
    AffineThreeFaceDecoder.decoder (faceMap p u) i =
      AffineThreeFaceDecoder.expression (p (origin 3) i)
        (if u 0 then p (basis 0) i else p (origin 3) i)
        (if u 1 then p (basis 1) i else p (origin 3) i)
        (if u 2 then p (basis 2) i else p (origin 3) i) := by
  simp only [AffineThreeFaceDecoder.decoder, faceMap, zeroFace_origin, zeroFace_basis]
  cases u 0 <;> cases u 1 <;> cases u 2 <;> rfl

/-- Every proper original character cancels across the eight signed faces;
the full character keeps precisely the signed seven-character bundle. -/
theorem port_charge_faces (p : Word 3 → Word n) (i : Fin n) (j : Fin 7) :
    (∑ u : Word 3, SignedCubeNormalizer.faceSign u *
      portCharge (AffineThreeFaceDecoder.decoder (faceMap p u) i) j) =
        portCharge (AffineThreeFaceDecoder.decoder p i) 6 * SignedCubeNormalizer.bundleSign j := by
  let b := p (origin 3) i
  let c₀ := p (basis 0) i
  let c₁ := p (basis 1) i
  let c₂ := p (basis 2) i
  let s := coefficientMask b c₀ c₁ c₂
  have hm (u : Word 3) : portCharge (AffineThreeFaceDecoder.decoder (faceMap p u) i) j =
      (if b then (-1 : ℤ) else 1) *
        (if SignedCubeNormalizer.intersection s u = SignedCubeNormalizer.bundleMask j
          then 1 else 0) := by
    rw [face_decoder, expression_charge, masked_coefficients]
  simp_rw [hm]
  calc
    _ = (if b then (-1 : ℤ) else 1) *
      SignedCubeNormalizer.signedIncidence s (SignedCubeNormalizer.bundleMask j) := by
        unfold SignedCubeNormalizer.signedIncidence
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro u hu
        split_ifs <;> ring
    _ = (if b then (-1 : ℤ) else 1) *
      (if s = SignedCubeNormalizer.topMask then SignedCubeNormalizer.bundleSign j else 0) := by
        rw [SignedCubeNormalizer.signedIncidence_bundle]
    _ = _ := by
      rw [AffineThreeFaceDecoder.decoder, expression_charge]
      change _ = (if b then (-1 : ℤ) else 1) *
        (if s = SignedCubeNormalizer.topMask then 1 else 0) * SignedCubeNormalizer.bundleSign j
      split_ifs <;> ring

/-- The signed eight-face product has the actual source boundary charge of
the full character, multiplied by each literal bundle sign. -/
theorem boundary_charge_faces (hk : 0 < k) (p : Word 3 → Word n) (j : Fin 7) :
    (∑ u : Word 3, (SignedCubeNormalizer.faceSign u : ZMod k) *
      boundaryCharge (faceMap p u) k j) =
        boundaryCharge p k 6 * (SignedCubeNormalizer.bundleSign j : ZMod k) := by
  simp_rw [boundaryCharge_eq_sum hk]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  have h := congrArg (fun a : ℤ => (a : ZMod k)) (port_charge_faces p i j)
  simpa only [Int.cast_sum, Int.cast_mul] using h

/-- The same cancellation stated directly with the eight genuine context
boundary degrees. -/
theorem boundary_degree_faces (hk : 0 < k) (p : Word 3 → Word n)
    (f : Signature Tractable.AlgebraicComplex n) (j : Fin 7) :
    (∑ u : Word 3, (SignedCubeNormalizer.faceSign u : ZMod k) *
      ((facePresentation p f k u).degree (Sum.inl j) : ZMod k)) =
        ((presentation p f k).degree (Sum.inl (6 : Fin 7)) : ZMod k) *
          (SignedCubeNormalizer.bundleSign j : ZMod k) := by
  calc
    _ = ∑ u : Word 3, (SignedCubeNormalizer.faceSign u : ZMod k) *
        boundaryCharge (faceMap p u) k j := by
      apply Finset.sum_congr rfl
      intro u hu
      congr 1
      exact (boundaryCharge_degree (faceMap p u) f k j).symm
    _ = boundaryCharge p k 6 * (SignedCubeNormalizer.bundleSign j : ZMod k) :=
      boundary_charge_faces hk p j
    _ = _ := by rw [boundaryCharge_degree p f k 6]

end
end Paper2.DegreeCSP.OriginalThreeFaceCharges
