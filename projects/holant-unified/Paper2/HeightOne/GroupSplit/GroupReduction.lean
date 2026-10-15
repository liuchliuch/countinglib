import Paper2.HeightOne.GroupSplit.AbstractSplit
import Paper2.HeightOne.GroupSplit.Extension
import Paper2.HeightOne.GroupSplit.Reversal
import Paper2.ExactInput.FixedFamilyField

/-! The finite group reduction for the complete actual transfer group. -/
namespace Paper2.HeightOne.GroupSplit
open MatrixGroup Tractable FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

lemma finite_actualClasses (P1 : Paper1Accepted) (F : SignatureFamily AlgebraicComplex)
    (hF : F.Finite) (hne : (actualTransfers F).Nonempty)
    (htorsion : ∀ B, ActualNonsingular F B → ProjectivelyFinite (transfer B)) :
    (actualClasses F).Finite := by
  letI : Finite F := hF.to_subtype
  let I := Σ f : F, Fin f.val.1 → Bool
  let coeff : I → AlgebraicComplex := fun p => p.1.val.2 p.2
  let L := Algebraic.familyField coeff
  have hL : FiniteDimensional ℚ L := Algebraic.familyField_finiteDimensional coeff
    (fun _ => Algebra.IsAlgebraic.isAlgebraic _)
  have hFin := P1.boundedTorsion_5_2 L hL F (by
    intro f hf x
    exact Algebraic.coefficient_mem_familyField coeff ⟨⟨f, hf⟩, x⟩) hne htorsion
  let hG := actualTransfers_projectiveMatrixGroup F hne htorsion
  rw [actualClasses_subgroup hG]
  letI := finite_projectiveSubgroup hG hFin
  exact Set.toFinite _

lemma weightedEquality_of_antidiagonal_class {F : SignatureFamily AlgebraicComplex}
    {q : PGL2 AlgebraicComplex} (hq : q ∈ actualClasses F)
    (hanti : q ∈ antidiagonalClasses) :
    ∃ f : Signature AlgebraicComplex 2, NetworkRealizable F f ∧ HeightTwo.WeightedEquality f := by
  obtain ⟨U, hU, rfl⟩ := hq
  obtain ⟨a, b, he⟩ := hanti
  obtain ⟨c, hc, hm⟩ := projectiveClass_eq_iff.mp (pglMk_eq_iff_projectiveClass_eq.mp he)
  apply weightedEquality_of_antidiagonal_transfer hU
  · simpa [antidiagonalGL, antidiagonal, Matrix.smul_apply] using
      congrArg (fun M : AMat => M false false) hm
  · simpa [antidiagonalGL, antidiagonal, Matrix.smul_apply] using
      congrArg (fun M : AMat => M true true) hm

lemma antidiagonal_of_extra {q : PGL2 AlgebraicComplex}
    (hsq : q * q = 1) (hne : q ≠ 1) (hnz : q ≠ zClass) (hcomm : Commute q zClass) :
    q ∈ antidiagonalClasses := by
  have hc : q ∈ diagonalClasses ∪ antidiagonalClasses := by
    rw [← centralizer_z]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  rcases hc with hd | ha
  · exact (hnz (diagonal_involution_unique hd (orderOf_eq_prime (by simpa [pow_two] using hsq) hne))).elim
  · exact ha

/-- The normalizer extension associated to all actual binaries. -/
def actualExtension (F : SignatureFamily AlgebraicComplex)
    (hG : ProjectiveMatrixGroup (actualTransfers F)) : Subgroup (PGL2 AlgebraicComplex) :=
  involutionExtension (projectiveSubgroup hG) zClass
    (by simpa only [pow_two] using zClass_square) (actualGroup_z_normalizes hG)

/-- Exhaustion of all finite-group cases. The last alternative is still purely
group-theoretic and keeps the distinguished reflection; it does not assume a basis. -/
theorem actual_group_reduction (P1 : Paper1Accepted) (F : SignatureFamily AlgebraicComplex)
    (hG : ProjectiveMatrixGroup (actualTransfers F)) (hfinite : (actualClasses F).Finite)
    (B : AMat) (hB : ActualNonsingular F B)
    (hB00 : B false false ≠ 0) (hB11 : B true true ≠ 0) :
    (∃ f : Signature AlgebraicComplex 2, NetworkRealizable F f ∧ HeightTwo.WeightedEquality f) ∨
    OddDihedralPresentation ((projectiveSubgroup hG).subgroupOf (actualExtension F hG))
      ⟨zClass, involution_mem_extension _ _ _ _⟩ := by
  let G := projectiveSubgroup hG
  let H := actualExtension F hG
  let J := G.subgroupOf H
  let z : H := ⟨zClass, involution_mem_extension _ _ _ _⟩
  have hfiniteG : (G : Set (PGL2 AlgebraicComplex)).Finite := by
    simpa only [G, ← actualClasses_subgroup hG] using hfinite
  have hfiniteH : (H : Set (PGL2 AlgebraicComplex)).Finite :=
    extension_finite G zClass _ _ hfiniteG
  have hzsq : z * z = 1 := by
    apply Subtype.ext
    change zClass * zClass = 1
    simpa only [pow_two] using zClass_square
  have hzne : z ≠ 1 := by
    intro hz
    have he : zClass = 1 := congrArg Subtype.val hz
    have ho := zClass_involution
    simp [he] at ho
  have hcover : Covered J z := fun x => x.property
  have htypes := finitePGLTypes_algebraic P1 H hfiniteH.to_subtype
  rcases finite_group_reduction J z hzsq hzne hcover htypes with hcentral | hextra | hodd
  · left
    let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B)
      (by rw [transfer, Matrix.det_mul]; exact mul_ne_zero hB.2 det_X_ne_zero)
    have huG : pglMk _ U ∈ G := ⟨U, ⟨B, hB, 1, one_ne_zero, by simp [U]⟩, rfl⟩
    let u : H := ⟨pglMk _ U, le_involutionExtension _ _ _ _ huG⟩
    have hc : Commute (pglMk _ U) zClass := congrArg Subtype.val (hcentral u huG).eq
    rcases (commute_z_iff_entries U).mp hc with ⟨h01, h10⟩ | ⟨h00, h11⟩
    · have hh : B false false = 0 := by
        simpa [U, transfer, X, Matrix.mul_apply, Signature.disequality] using h01
      exact (hB00 hh).elim
    · exact weightedEquality_of_antidiagonal_transfer
        (show transfer B ∈ actualTransfers F from ⟨B, hB, 1, one_ne_zero, by simp⟩) h00 h11
  · left
    obtain ⟨u, hu, husq, huone, huz, hucomm⟩ := hextra
    have huc : (u : PGL2 AlgebraicComplex) ∈ actualClasses F := by
      rw [actualClasses_subgroup hG]
      exact hu
    apply weightedEquality_of_antidiagonal_class huc
    exact antidiagonal_of_extra (congrArg Subtype.val husq)
      (fun h => huone (Subtype.ext h)) (fun h => huz (Subtype.ext h))
      (congrArg Subtype.val hucomm.eq)
  · exact Or.inr hodd

end
end Paper2.HeightOne.GroupSplit
