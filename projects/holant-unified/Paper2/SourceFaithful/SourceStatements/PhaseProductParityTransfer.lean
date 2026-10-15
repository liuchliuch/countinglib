import Paper2.SourceFaithful.SourceStatements.TypeParityStatement
import Paper2.SourceFaithful.SourceStatements.PhaseProductParityBinaryShape

/-! The exact binary condition in source Proposition 5.13: literal Walsh
transfer membership in the dihedral group is precisely the nonzero local
negative-root complementary-pair condition. All scales and orientations are
retained, including the inverse root when the complementary offset reverses. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards
open HeightOne.GroupSplit HeightOne.GroupSplit.MatrixGroup
open HeightOne.GroupSplit.FiniteGroupFacts.ProjectiveCentralizers
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private lemma not_pair (a b : Bool) :
    (fun i => !(![a,b] : Fin 2 → Bool) i) = ![!a,!b] := by
  funext i
  fin_cases i <;> rfl

private lemma diagonal_transfer_pair {M : AMat} {c s : AlgebraicComplex}
    (h : M * (zGL : AMat) = c • diagonal 1 s) :
    binarySignature M = c • twoPoint ![false,false] (-s) := by
  have hm : M = tableBinary (c • twoPoint ![false,false] (-s)) := by
    funext i j
    have he := congrArg (fun A : AMat => A i j) h
    cases i <;> cases j <;>
      simp [Matrix.mul_apply,zGL,diagonalGL,diagonal,tableBinary,
        twoPoint,point,not_pair] at he ⊢ <;>
          first | linear_combination he | linear_combination -he
  rw [hm,binarySignature_tableBinary]

private lemma reflection_transfer_pair {M : AMat} {c s : AlgebraicComplex}
    (h : M * (zGL : AMat) = c • (X * diagonal 1 s)) :
    binarySignature M = c • twoPoint ![true,false] (-s) := by
  have hm : M = tableBinary (c • twoPoint ![true,false] (-s)) := by
    funext i j
    have he := congrArg (fun A : AMat => A i j) h
    cases i <;> cases j <;>
      simp [Matrix.mul_apply,zGL,diagonalGL,diagonal,X,Signature.disequality,
        tableBinary,twoPoint,point,not_pair] at he ⊢ <;>
          first | linear_combination he | linear_combination -he
  rw [hm,binarySignature_tableBinary]

private lemma walsh_binary_table (f : Signature AlgebraicComplex 2) :
    tableBinary (walshCoordinates f) = walshBinary (tableBinary f) := by
  have h := walshCoordinates_binary (tableBinary f)
  rw [binarySignature_tableBinary] at h
  funext i j
  exact congrFun h ![i,j]

private lemma nonzero_walsh {f : Signature AlgebraicComplex 2} (hf : f ≠ 0) :
    walshCoordinates f ≠ 0 := by
  intro hz
  apply hf
  exact (Conformal.action_eq_zero_iff walshBasis.symm f).mp
    (by simpa only [walshBasis_inverse_action] using hz)

private lemma pair_transfer_member {N : ℕ} (hN : 0 < N) (a : Fin 2 → Bool)
    (c s : AlgebraicComplex) (hc : c ≠ 0) (hs : Root N s) :
    TypeParityStatement.WalshTransferMember .dihedral N
      (tableBinary (action walsh (c • twoPoint a (-s)))) := by
  classical
  let : NeZero N := ⟨by omega⟩
  have hs0 := root_ne_zero hN hs
  have hsi : Root N s⁻¹ := by change (s⁻¹) ^ N = 1; rw [inv_pow,hs,inv_one]
  let u : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs
  let v : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s⁻¹ hsi
  have hu : (u.val : AlgebraicComplex) = s := rootsOfUnity.coe_mkOfPowEq hs
  have hv : (v.val : AlgebraicComplex) = s⁻¹ := rootsOfUnity.coe_mkOfPowEq hsi
  have hw : walshBinary (tableBinary (action walsh (c • twoPoint a (-s)))) =
      tableBinary (c • twoPoint a (-s)) := by
    rw [← walsh_binary_table,walsh_inv_action_cancel]
  rw [TypeParityStatement.WalshTransferMember,hw]
  have ha : a = ![a 0,a 1] := by funext i; fin_cases i <;> simp
  rw [ha]
  cases h0 : a 0 <;> cases h1 : a 1
  · left
    refine ⟨u,c,hc,?_⟩
    rw [hu]
    funext i j
    cases i <;> cases j <;>
      simp [tableBinary,twoPoint,point,not_pair,Matrix.mul_apply,zGL,diagonalGL,diagonal]
  · right
    refine ⟨rfl,v,-c*s,mul_ne_zero (neg_ne_zero.mpr hc) hs0,?_⟩
    rw [hv]
    funext i j
    cases i <;> cases j <;>
      simp [tableBinary,twoPoint,point,not_pair,Matrix.mul_apply,zGL,diagonalGL,diagonal,
        X,Signature.disequality,hs0]
  · right
    refine ⟨rfl,u,c,hc,?_⟩
    rw [hu]
    funext i j
    cases i <;> cases j <;>
      simp [tableBinary,twoPoint,point,not_pair,Matrix.mul_apply,zGL,diagonalGL,diagonal,
        X,Signature.disequality]
  · left
    refine ⟨v,-c*s,mul_ne_zero (neg_ne_zero.mpr hc) hs0,?_⟩
    rw [hv]
    funext i j
    cases i <;> cases j <;>
      simp [tableBinary,twoPoint,point,not_pair,Matrix.mul_apply,zGL,diagonalGL,diagonal,
        hs0]

/-- Exact source condition (C) for a nonzero binary factor. The Walsh transfer
is in D₂N precisely when the Walsh table is a live negative-root pair. -/
theorem walshTransfer_dihedral_iff {N : ℕ} (hN : 0 < N)
    (f : Signature AlgebraicComplex 2) :
    TypeParityStatement.WalshTransferMember .dihedral N (tableBinary f) ↔
      f ≠ 0 ∧ BinaryPhase N (walshCoordinates f) := by
  classical
  constructor
  · intro h
    have hf : f ≠ 0 := by
      intro hz
      subst f
      rcases h with ⟨s,c,hc,ht⟩ | ⟨_,s,c,hc,ht⟩
      · have he := congrArg (fun A : AMat => A false false) ht
        simp [walshBinary,tableBinary,Matrix.mul_apply,zGL,diagonalGL,diagonal] at he
        exact hc he.symm
      · have he := congrArg (fun A : AMat => A true false) ht
        simp [walshBinary,tableBinary,Matrix.mul_apply,zGL,diagonalGL,diagonal,
          X,Signature.disequality] at he
        exact hc he.symm
    refine ⟨hf,?_⟩
    apply (binary_phase_iff_pair hN (by simp) (walshCoordinates f)).mpr
    rcases h with ⟨s,c,hc,ht⟩ | ⟨_,s,c,hc,ht⟩
    · refine Or.inr ⟨![false,false],c,s.val,hc,root_of_unity s,?_⟩
      have hp := diagonal_transfer_pair ht
      have hw := walshCoordinates_binary (tableBinary f)
      rw [binarySignature_tableBinary] at hw
      exact hw.trans hp
    · refine Or.inr ⟨![true,false],c,s.val,hc,root_of_unity s,?_⟩
      have hp := reflection_transfer_pair ht
      have hw := walshCoordinates_binary (tableBinary f)
      rw [binarySignature_tableBinary] at hw
      exact hw.trans hp
  · rintro ⟨hf,h⟩
    rcases (binary_phase_iff_pair hN (by simp) (walshCoordinates f)).mp h with
      hz | ⟨a,c,s,hc,hs,hw⟩
    · exact False.elim (nonzero_walsh hf hz)
    · have he : f = action walsh (c • twoPoint a (-s)) := by
        rw [← hw,walsh_action_cancel]
      rw [he]
      exact pair_transfer_member hN a c s hc hs

/-- The cyclic dictionary retains parity zero as well as the exact
complementary-entry root ratio. A reflection cannot satisfy parity zero
because its literal off-diagonal entry has a nonzero projective scale. -/
theorem walshTransfer_cyclic_iff {N : ℕ} (hN : 0 < N)
    (f : Signature AlgebraicComplex 2) :
    TypeParityStatement.WalshTransferMember .cyclic N (tableBinary f) ↔
      f ≠ 0 ∧ SupportedOnParity (walshCoordinates f) 0 ∧
        ∀ x, RootComplement N (walshCoordinates f x)
          (walshCoordinates f (fun i => !(x i))) := by
  classical
  constructor
  · intro h
    have hd : TypeParityStatement.WalshTransferMember .dihedral N (tableBinary f) := by
      rcases h with h | ⟨he,_⟩
      · exact Or.inl h
      · cases he
    obtain ⟨hf,hb⟩ := (walshTransfer_dihedral_iff hN f).mp hd
    have hp := TypeParityStatement.binary_parity f h
    exact ⟨hf,hp,hb.2⟩
  · rintro ⟨hf,hp,hr⟩
    have hd := (walshTransfer_dihedral_iff hN f).mpr
      ⟨hf,supportedOnParity_hasParity hp,hr⟩
    rcases hd with h | ⟨_,s,c,hc,ht⟩
    · exact Or.inl h
    · have hw : walshCoordinates f = c • twoPoint ![true,false] (-s.val) := by
        have hh := walshCoordinates_binary (tableBinary f)
        rw [binarySignature_tableBinary] at hh
        exact hh.trans (reflection_transfer_pair ht)
      have hval : walshCoordinates f ![true,false] ≠ 0 := by
        rw [hw]
        simpa [twoPoint,point,not_pair] using hc
      have he := hp ![true,false] hval
      have hn : parity (![true,false] : Fin 2 → Bool) ≠ 0 := by decide
      exact False.elim (hn he)

/-- Literal transfer membership forces nonsingularity of the original
binary coefficient matrix, before the Walsh change of coordinates. -/
theorem walshTransfer_nonsingular {kind : TypeParityStatement.GroupKind} {N : ℕ}
    (hN : 0 < N) (f : Signature AlgebraicComplex 2)
    (h : TypeParityStatement.WalshTransferMember kind N (tableBinary f)) :
    (tableBinary f).det ≠ 0 := by
  intro hz
  have hl : (walshBinary (tableBinary f) * (zGL : AMat)).det = 0 := by
    simp [walshBinary,Matrix.det_mul,hz]
  rcases h with ⟨s,c,hc,ht⟩ | ⟨_,s,c,hc,ht⟩
  · have hr : (c • diagonal 1 (s.val : AlgebraicComplex)).det =
        c * c * (s.val : AlgebraicComplex) := by
      rw [determinant_bool]
      simp [diagonal]
      ring
    have he := congrArg Matrix.det ht
    rw [hl,hr] at he
    exact mul_ne_zero (mul_ne_zero hc hc) (root_ne_zero hN (root_of_unity s)) he.symm
  · have hr : (c • (X * diagonal 1 (s.val : AlgebraicComplex))).det =
        -(c * c * (s.val : AlgebraicComplex)) := by
      rw [determinant_bool]
      simp [diagonal,X,Signature.disequality,Matrix.mul_apply]
      ring
    have he := congrArg Matrix.det ht
    rw [hl,hr] at he
    exact (neg_ne_zero.mpr
      (mul_ne_zero (mul_ne_zero hc hc) (root_ne_zero hN (root_of_unity s)))) he.symm

theorem walshTransfer_dihedral_nonsingular {N : ℕ} (hN : 0 < N)
    (f : Signature AlgebraicComplex 2)
    (h : TypeParityStatement.WalshTransferMember .dihedral N (tableBinary f)) :
    (tableBinary f).det ≠ 0 := walshTransfer_nonsingular hN f h

theorem walshTransfer_cyclic_nonsingular {N : ℕ} (hN : 0 < N)
    (f : Signature AlgebraicComplex 2)
    (h : TypeParityStatement.WalshTransferMember .cyclic N (tableBinary f)) :
    (tableBinary f).det ≠ 0 := walshTransfer_nonsingular hN f h

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity

