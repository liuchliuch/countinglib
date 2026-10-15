import Paper2.HeightOne.GroupSplit.NormalizedGroup

/-! Paper 2 Theorem 5.4, relative only to the named Paper 1 clauses. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.GroupSplit
open MatrixGroup Tractable FiniteGroupFacts.ProjectiveCentralizers
noncomputable section

lemma networkRealizable_of_mem {F : SignatureFamily AlgebraicComplex} {n : ℕ}
    {f : Signature AlgebraicComplex n} (hf : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NetworkRealizable F f := by
  let e : (Σ _ : Unit, Fin n) ≃ Fin n := {
    toFun := fun p => p.2
    invFun := fun i => ⟨(), i⟩
    left_inv := by rintro ⟨u, i⟩; cases u; rfl
    right_inv := fun _ => rfl }
  have h := NetworkRealizable.piTensor (F := F) (fun _ : Unit => n) (fun _ => f) (fun _ => hf)
  have hh := h.reindex e
  have heq : Tensor.reindex e (Tensor.piTensor (fun _ : Unit => f)) = f := by
    funext x
    simp [Tensor.reindex, Tensor.piTensor, e]
  exact heq ▸ hh

def AllBinariesSafe (F : SignatureFamily AlgebraicComplex) : Prop :=
  ∀ B : AMat, NetworkRealizable F (binarySignature B) → B ≠ 0 →
    Matrix.det B ≠ 0 ∧ ProjectivelyFinite (transfer B)


/-- Safety of every nonzero binary is preserved by the one legal normalization,
so the resulting complete transfer set really is the source's safe binary group. -/
theorem AllBinariesSafe.diagonal {F : SignatureFamily AlgebraicComplex}
    (hsafe : AllBinariesSafe F) (hG : ProjectiveMatrixGroup (actualTransfers F))
    (hfinite : (actualClasses F).Finite) (D : InvertibleKernel) (a b : AlgebraicComplex)
    (hD : D.matrix = diagonalKernel a b) (ha : a ≠ 0) (hb : b ≠ 0) :
    AllBinariesSafe (familyAction D F) := by
  intro B hB hBne
  have hdet : Matrix.det B ≠ 0 := nonsingular_after_diagonal F
    (fun C hC hCne => (hsafe C hC hCne).1) D a b hD ha hb B hB hBne
  refine ⟨hdet, ?_⟩
  let U := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer B)
    (by rw [transfer, Matrix.det_mul]; exact mul_ne_zero hdet det_X_ne_zero)
  let C : MulAut (PGL2 AlgebraicComplex) := MulAut.conj (pglMk _ (basisGL D))
  let G' := (projectiveSubgroup hG).map C.toMonoidHom
  have hset : actualClasses (familyAction D F) = (G' : Set (PGL2 AlgebraicComplex)) := by
    rw [completeClasses_diagonal_transport F D a b hD ha hb]
    rfl
  have hfin : (G' : Set (PGL2 AlgebraicComplex)).Finite := by
    rw [← hset, completeClasses_diagonal_transport F D a b hD ha hb]
    exact hfinite.image _
  letI : Finite G' := hfin.to_subtype
  have hu : pglMk _ U ∈ G' := by
    change pglMk _ U ∈ (G' : Set (PGL2 AlgebraicComplex))
    rw [← hset]
    exact ⟨U, ⟨B, ⟨hB, hdet⟩, 1, one_ne_zero, by simp [U]⟩, rfl⟩
  obtain ⟨k, hk, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp
    (isOfFinOrder_of_finite (⟨pglMk _ U, hu⟩ : G'))
  have huFin : IsOfFinOrder (pglMk _ U) := isOfFinOrder_iff_pow_eq_one.mpr
    ⟨k, hk, congrArg Subtype.val hpow⟩
  exact (isOfFinOrder_pglMk_iff U).mp huFin

def WeightedEqualityReachable (F : SignatureFamily AlgebraicComplex) : Prop :=
  ∃ f : Signature AlgebraicComplex 2, NetworkRealizable F f ∧ HeightTwo.WeightedEquality f

def OddNormalized (F : SignatureFamily AlgebraicComplex) : Prop :=
  ∃ (N : ℕ) (q : AlgebraicComplex) (D : InvertibleKernel),
    3 ≤ N ∧ Odd N ∧ q ≠ 0 ∧ D.matrix = diagonalKernel q 1 ∧ XConformal D ∧
    AllBinariesSafe (familyAction D F) ∧
    Xor (actualClasses (familyAction D F) = cyclicPhaseClasses N)
      (actualClasses (familyAction D F) = dihedralPhaseClasses N) ∧
    ∃ rep : actualClasses (familyAction D F) → AMat,
      ∀ u : actualClasses (familyAction D F),
        ActualNonsingular (familyAction D F) (rep u) ∧
          projectiveClass (transfer (rep u)) = pglToProjectiveClass u

/-- Source Theorem 5.4. The family is finite and algebraic; the distinguished
height-one mountain is a member with both nonzero endpoints; safety concerns
all actual ordered binaries. The resulting D is one legal diagonal basis, and
all displayed classes retain actual graph representatives. -/
theorem finite_group_split (P1 : Paper1Accepted)
    (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (B : AMat) (hBmem : (⟨2, binarySignature B⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hB00 : B false false ≠ 0) (hB11 : B true true ≠ 0) (hsafe : AllBinariesSafe F) :
    WeightedEqualityReachable F ∨ OddNormalized F := by
  have hBr : NetworkRealizable F (binarySignature B) := networkRealizable_of_mem hBmem
  have hBne : B ≠ 0 := by intro h; exact hB00 (congrArg (fun M : AMat => M false false) h)
  have hB : ActualNonsingular F B := ⟨hBr, (hsafe B hBr hBne).1⟩
  have hne : (actualTransfers F).Nonempty :=
    ⟨transfer B, B, hB, 1, one_ne_zero, by simp⟩
  have htorsion : ∀ C, ActualNonsingular F C → ProjectivelyFinite (transfer C) := by
    intro C hC
    apply (hsafe C hC.1 ?_).2
    intro hz
    exact hC.2 (by rw [hz, Matrix.det_zero])
  let hG := actualTransfers_projectiveMatrixGroup F hne htorsion
  have hfinite := finite_actualClasses P1 F hF hne htorsion
  rcases actual_group_reduction P1 F hG hfinite B hB hB00 hB11 with hEq | hOdd
  · exact Or.inl hEq
  · right
    let G := projectiveSubgroup hG
    let H := actualExtension F hG
    let z : H := ⟨zClass, involution_mem_extension _ _ _ _⟩
    have hzsq : z * z = 1 := by
      apply Subtype.ext
      change zClass * zClass = 1
      simpa only [pow_two] using zClass_square
    obtain ⟨N, hN, hodd, r, hr⟩ := hOdd.rotation hzsq
    have hIncl : G ≤ H := le_involutionExtension _ _ _ _
    have hrot : RotationData G zClass N (r : PGL2 AlgebraicComplex) := by
      have hh := hr.map H.subtype Subtype.val_injective
      change RotationData ((G.subgroupOf H).map H.subtype) zClass N (r : PGL2 AlgebraicComplex) at hh
      rwa [Subgroup.map_subgroupOf_eq_of_le hIncl] at hh
    obtain ⟨q, D, hq, hD, hconf, hsets⟩ := normalize_complete_odd_group F hG N hN hodd r hrot
    exact ⟨N, q, D, hN, hodd, hq, hD, hconf,
      hsafe.diagonal hG hfinite D q 1 hD hq one_ne_zero, normalized_forms_exclusive hsets,
      fixed_actualClass_representatives _⟩


/-- The same theorem with the literal source mountain predicate. -/
theorem finite_group_split_height_one (P1 : Paper1Accepted)
    (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    (B : AMat) (hBmem : (⟨2, binarySignature B⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hB : IsMountain (d := 1) (binarySignature B)) (hsafe : AllBinariesSafe F) :
    WeightedEqualityReachable F ∨ OddNormalized F :=
  finite_group_split P1 F hF B hBmem hB.zero_ne_zero hB.one_ne_zero hsafe

end
end Paper2.HeightOne.GroupSplit
