import Paper2.HeightOne.GroupSplit.PGL
import Paper2.NetworkSubstitution
import Paper2.HeightTwo

/-! All actual resource-labelled ordered binaries, with their literal transfer
matrices. No enumeration or abstract gadget-closure predicate defines this set. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.GroupSplit
open MatrixGroup
noncomputable section
variable {K : Type} [Field K]

def binarySignature (B : Binary (K := K)) : Signature K 2 := fun x => B (x 0) (x 1)

def ActualNonsingular (F : SignatureFamily K) (B : Binary (K := K)) : Prop :=
  NetworkRealizable F (binarySignature B) ∧ Matrix.det B ≠ 0

def actualTransfers (F : SignatureFamily K) : Set (Binary (K := K)) :=
  {T | ∃ B, ActualNonsingular F B ∧ ∃ c : K, c ≠ 0 ∧ T = c • transfer B}

/-- The two vertices and one native-X edge of an actual ordered series splice. -/
def seriesOuter (B C : Binary (K := K)) : FiniteNetwork K Bool Unit 2 where
  arity := fun _ => 2
  ports := {
    toFun := fun p => if p.1 then
      (if p.2 = 0 then .inr ((), true) else .inl 1)
      else (if p.2 = 0 then .inl 0 else .inr ((), false))
    invFun := Sum.elim (fun i => if i = 0 then ⟨false, 0⟩ else ⟨true, 1⟩)
      (fun p => if p.2 then ⟨true, 0⟩ else ⟨false, 1⟩)
    left_inv := by rintro ⟨v, i⟩; cases v <;> fin_cases i <;> rfl
    right_inv := by
      rintro (i | ⟨u, b⟩)
      · fin_cases i <;> rfl
      · cases u; cases b <;> rfl }
  vertex := fun v => if v then binarySignature C else binarySignature B
  edge := fun _ => Signature.disequality

lemma seriesOuter_denote (B C : Binary (K := K)) :
    (seriesOuter B C).toNetwork.denote = binarySignature (B * X * C) := by
  classical
  letI : DecidableEq Unit := fun _ _ => Classical.propDecidable _
  rw [FiniteNetwork.denote_toNetwork]
  funext x
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  calc
    _ = ∑ t : Bool, B (x 0) t * C (!t) (x 1) := by
      apply Fintype.sum_equiv (Equiv.funUnique Unit Bool)
      intro z
      simp [seriesOuter, binarySignature, Equiv.funUnique, Equiv.piUnique, mul_comm]
    _ = _ := by
      simp [binarySignature, Matrix.mul_apply, X, Signature.disequality, Fintype.sum_bool]
      ring

lemma realizes_series {F : SignatureFamily K} {B C : Binary (K := K)}
    (hB : NetworkRealizable F (binarySignature B))
    (hC : NetworkRealizable F (binarySignature C)) :
    NetworkRealizable F (binarySignature (B * X * C)) := by
  rw [← seriesOuter_denote]
  apply NetworkRealizable.substitute
  · intro e; rfl
  · intro v
    change NetworkRealizable F (if (Fintype.equivFin Bool).symm v then
      binarySignature C else binarySignature B)
    split <;> assumption

lemma det_X_ne_zero : Matrix.det (X : Binary (K := K)) ≠ 0 := by
  have h := congrArg Matrix.det (X_mul_X (K := K))
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro hz
  simp [hz] at h

lemma ActualNonsingular.series {F : SignatureFamily K} {B C : Binary (K := K)}
    (hB : ActualNonsingular F B) (hC : ActualNonsingular F C) :
    ActualNonsingular F (B * X * C) := by
  refine ⟨realizes_series hB.1 hC.1, ?_⟩
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero hB.2 det_X_ne_zero) hC.2

lemma transfer_series (B C : Binary (K := K)) :
    transfer (B * X * C) = transfer B * transfer C := by
  simp only [transfer, Matrix.mul_assoc]

lemma actualTransfers_mul {F : SignatureFamily K} {U V : Binary (K := K)}
    (hU : U ∈ actualTransfers F) (hV : V ∈ actualTransfers F) : U * V ∈ actualTransfers F := by
  obtain ⟨B, hB, c, hc, rfl⟩ := hU
  obtain ⟨C, hC, d, hd, rfl⟩ := hV
  refine ⟨B * X * C, hB.series hC, c * d, mul_ne_zero hc hd, ?_⟩
  rw [transfer_series, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

lemma actualTransfers_scale {F : SignatureFamily K} {T : Binary (K := K)}
    (hT : T ∈ actualTransfers F) {c : K} (hc : c ≠ 0) : c • T ∈ actualTransfers F := by
  obtain ⟨B, hB, d, hd, rfl⟩ := hT
  exact ⟨B, hB, c * d, mul_ne_zero hc hd, smul_smul _ _ _⟩

/-- The group structure follows from real series gadgets and positive torsion
powers. The separate arithmetic finiteness assertion is not assumed here. -/
theorem actualTransfers_projectiveMatrixGroup (F : SignatureFamily K)
    (hne : (actualTransfers F).Nonempty)
    (htorsion : ∀ B, ActualNonsingular F B → ProjectivelyFinite (transfer B)) :
    ProjectiveMatrixGroup (actualTransfers F) := by
  apply projectiveMatrixGroup_of_torsion hne
  · exact fun _ hU _ hV => actualTransfers_mul hU hV
  · exact fun _ hT _ hc => actualTransfers_scale hT hc
  · rintro T ⟨B, hB, c, hc, rfl⟩
    exact (htorsion B hB).smul hc


lemma determinant_bool (B : Binary (K := K)) :
    Matrix.det B = B false false * B true true - B false true * B true false := by
  rw [← Matrix.det_reindex_self (e := finTwoEquiv.symm), Matrix.det_fin_two]
  simp [Matrix.reindex, Matrix.submatrix, finTwoEquiv]

/-- An antidiagonal transfer class in the complete actual group provides a
literal actual weighted equality, with both nonzero diagonal entries. -/
theorem weightedEquality_of_antidiagonal_transfer {F : SignatureFamily K}
    {T : Binary (K := K)} (hT : T ∈ actualTransfers F)
    (h00 : T false false = 0) (h11 : T true true = 0) :
    ∃ f : Signature K 2, NetworkRealizable F f ∧ HeightTwo.WeightedEquality f := by
  obtain ⟨B, hB, c, hc, rfl⟩ := hT
  have h01 : B false true = 0 := by
    have h : c * B false true = 0 := by
      simpa [Matrix.smul_apply, transfer, X, Matrix.mul_apply, Signature.disequality] using h00
    exact (mul_eq_zero.mp h).resolve_left hc
  have h10 : B true false = 0 := by
    have h : c * B true false = 0 := by
      simpa [Matrix.smul_apply, transfer, X, Matrix.mul_apply, Signature.disequality] using h11
    exact (mul_eq_zero.mp h).resolve_left hc
  have hd : B false false * B true true ≠ 0 := by
    simpa only [determinant_bool, h01, zero_mul, sub_zero] using hB.2
  exact ⟨binarySignature B, hB.1, h01, h10,
    (mul_ne_zero_iff.mp hd).1, (mul_ne_zero_iff.mp hd).2⟩

lemma binarySignature_transpose (B : Binary (K := K)) :
    binarySignature B.transpose =
      Tensor.reindex (Equiv.swap (0 : Fin 2) 1) (binarySignature B) := by
  funext x
  simp [binarySignature, Tensor.reindex, Matrix.transpose_apply]

lemma actualNonsingular_transpose {F : SignatureFamily K} {B : Binary (K := K)}
    (hB : ActualNonsingular F B) : ActualNonsingular F B.transpose := by
  constructor
  · rw [binarySignature_transpose]
    exact hB.1.reindex _
  · simpa only [Matrix.det_transpose] using hB.2

lemma actualTransfers_reversal (F : SignatureFamily K) : ReversalStable (actualTransfers F) := by
  rintro T ⟨B, hB, c, hc, rfl⟩
  refine ⟨B.transpose, actualNonsingular_transpose hB, c, hc, ?_⟩
  rw [transfer_transpose]
  simp only [reverseTransfer, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]

end
end Paper2.HeightOne.GroupSplit
