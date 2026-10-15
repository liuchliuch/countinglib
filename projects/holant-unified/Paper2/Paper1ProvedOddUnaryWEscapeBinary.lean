import Paper2.Paper1ProvedOddUnaryWEscape
import Paper2.Paper1ProvedOddUnaryTernaryBinary

/-! Exact matching-orientation tests for ordinary binaries, and selection of
that orientation from an actual nonzero isotropic repeated W column. -/
namespace Paper2.Paper1Proved.OddUnary.WEscape
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem oneHot_binary_iff (f : Holant.Signature AlgebraicComplex 2) :
    Holant.Signature.OneHot f ↔ f ![true,true]=0 := by
  constructor
  · intro h
    exact h _ (by decide)
  · intro h x hx
    have he : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
    rw [he] at hx ⊢
    cases h0 : x 0 <;> cases h1 : x 1
    · simp only [h0,h1] at hx ⊢
      exact ((by decide : ¬1 < Holant.weight (![false,false] : Fin 2 → Bool)) hx).elim
    · simp only [h0,h1] at hx ⊢
      exact ((by decide : ¬1 < Holant.weight (![false,true] : Fin 2 → Bool)) hx).elim
    · simp only [h0,h1] at hx ⊢
      exact ((by decide : ¬1 < Holant.weight (![true,false] : Fin 2 → Bool)) hx).elim
    · simpa only [h0,h1] using h

private theorem matchingImage_iff_inverse (opposite : Bool) {n : ℕ}
    (f : Holant.Signature AlgebraicComplex n) :
    matchingImage opposite n f ↔ Holant.Signature.OneHot
      ((TensorDecisionMatching.basis opposite).symm.action f) := by
  constructor
  · exact TensorDecisionMatching.inverse_factor opposite n f
  · intro h
    have hh := TensorDecisionMatching.forward_factor opposite n
      ((TensorDecisionMatching.basis opposite).symm.action f) h
    simpa only [InvertibleKernel.action_symm_action] using hh

/-- The last inverse-coordinate binary entry is the ordinary pairing along
its selected isotropic source-K column. -/
theorem inverse_binary_entry (opposite : Bool) (T : Holant.Kernel AlgebraicComplex) :
    ((TensorDecisionMatching.basis opposite).symm.action (kernelSignature T)) ![true,true]=
      TernaryW.column_pairing T (TensorDecisionMatching.basis opposite).matrix
        (TensorDecisionMatching.basis opposite).matrix := by
  rw [InvertibleKernel.action,coordinateAction_kernelSignature]
  cases opposite <;>
    simp [TensorDecisionMatching.basis,InvertibleKernel.symm,InvertibleKernel.comp,
      sourceKBasis,bitFlipBasis,KMatrix,KInverse,Holant.Kernel.mul_apply,Holant.Kernel.transpose,
      Holant.Signature.disequality,kernelSignature,TernaryW.column_pairing]
  all_goals ring

theorem matchingImage_binary_iff (opposite : Bool) (T : Holant.Kernel AlgebraicComplex) :
    matchingImage opposite 2 (kernelSignature T) ↔
      TernaryW.column_pairing T (TensorDecisionMatching.basis opposite).matrix
        (TensorDecisionMatching.basis opposite).matrix=0 := by
  rw [matchingImage_iff_inverse,oneHot_binary_iff,inverse_binary_entry]

private theorem sqrtTwo_nonzero : (sqrtTwo : AlgebraicComplex) ≠ 0 := by
  intro hz
  have hs := sqrtTwo_sq
  rw [hz] at hs
  norm_num at hs

/-- A nonzero isotropic vector determines one of the two fixed source-K
orientations, retaining its exact nonzero proportionality scalar. -/
theorem isotropic_orientation (A : Holant.Kernel AlgebraicComplex)
    (h0 : A false false ≠ 0)
    (iso : A false false^2+A true false^2=0) :
    ∃ opposite : Bool, ∃ c : AlgebraicComplex, c ≠ 0 ∧
      ∀ v, A v false=c*(TensorDecisionMatching.basis opposite).matrix v false := by
  have fact : (A true false-imaginaryUnit*A false false)*
      (A true false+imaginaryUnit*A false false)=0 := by
    calc
      _ = A true false^2-imaginaryUnit^2*A false false^2 := by ring
      _ = 0 := by rw [imaginaryUnit_sq]; linear_combination iso
  have hc : A false false*sqrtTwo ≠ 0 := mul_ne_zero h0 sqrtTwo_nonzero
  rcases mul_eq_zero.mp fact with h | h
  · refine ⟨false,A false false*sqrtTwo,hc,?_⟩
    intro v
    cases v <;>
      simp [TensorDecisionMatching.basis,sourceKBasis,KMatrix]
    · field_simp [sqrtTwo_nonzero]
    · field_simp [sqrtTwo_nonzero]
      linear_combination h
  · refine ⟨true,A false false*sqrtTwo,hc,?_⟩
    intro v
    cases v <;>
      simp [TensorDecisionMatching.basis,sourceKBasis,bitFlipBasis,InvertibleKernel.comp,
        Holant.Kernel.mul_apply,Holant.Signature.disequality,KMatrix]
    · field_simp [sqrtTwo_nonzero]
    · field_simp [sqrtTwo_nonzero]
      linear_combination h

/-- Once a binary violates that matching orientation, its same-table physical
matrix really breaks the common repeated line. -/
theorem binary_outside_breaks (A T : Holant.Kernel AlgebraicComplex)
    (opposite : Bool) (c : AlgebraicComplex) (hc : c ≠ 0)
    (line : ∀ v, A v false=c*(TensorDecisionMatching.basis opposite).matrix v false)
    (outside : ¬ matchingImage opposite 2 (kernelSignature T)) :
    TernaryW.column_pairing T A A ≠ 0 := by
  have hb : TernaryW.column_pairing T (TensorDecisionMatching.basis opposite).matrix
      (TensorDecisionMatching.basis opposite).matrix ≠ 0 := by
    rwa [matchingImage_binary_iff] at outside
  rw [TernaryW.column_pairing_common T _ A A c c line line]
  exact mul_ne_zero (mul_ne_zero hc hc) hb

/-- Consume the arity-two branch of the physical outside-matching selector
using the genuine nonsingular matrix of its prime graph. -/
theorem outside_binary_hard {L : Paper2.ExactInput.Language} (S : IsotropicWSource L)
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted)
    (N : OrdinaryNegativeCubicGadgets.Macro S.source.H 3)
    (A B C : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature S.source.K.subtype N.network.denote=
      TernaryW.W.image A.matrix B.matrix C.matrix)
    (bc : TernaryW.W.gram (1 : AlgebraicComplex) B.matrix C.matrix false false=0)
    (ab : TernaryW.W.gram 1 A.matrix B.matrix false false=0)
    (ca : TernaryW.W.gram 1 C.matrix A.matrix false false=0)
    (opposite : Bool) (c : AlgebraicComplex) (hc : c ≠ 0)
    (line : ∀ v, A.matrix v false=c*(TensorDecisionMatching.basis opposite).matrix v false)
    (V : NoXOrdinaryGraphAdjoin.Output S.source.H 2)
    (prime : Prime (⟨2,V.network.denote⟩ : Holant.AnySignature S.source.K))
    (outside : ¬ matchingImage opposite 2
      (RingHomRealization.mapSignature S.source.K.subtype V.network.denote)) :
    Paper2.FixedFieldOutput.SharpPHard .ordinary L := by
  let _ : Algebra ℚ S.source.K := S.source.K.algebra'
  let g := RingHomRealization.mapSignature S.source.K.subtype V.network.denote
  let D := binaryMatrix g
  have pg : Prime (⟨2,g⟩ : Holant.AnySignature AlgebraicComplex) :=
    (prime_mapSignature_iff S.source.K.subtype _).mpr prime
  have hd : Matrix.det D ≠ 0 := prime_binary_nonsingular D
    (by rw [binarySignature_binaryMatrix]; exact pg)
  have hdet : Holant.Tractable.SymmetricBinaryPullback.determinant D ≠ 0 := by
    rwa [binary_det_formula] at hd
  let T := Holant.Tractable.SymmetricBinaryPullback.invertibleOfDeterminant D hdet
  let binary : OrdinaryNegativeCubicGadgets.Macro S.source.H 2 :=
    ⟨V.network,V.labels,V.exact,V.ordinary⟩
  have binaryForm : RingHomRealization.mapSignature S.source.K.subtype binary.network.denote=
      kernelSignature T.matrix := by
    funext x
    change g x=g ![x 0,x 1]
    congr 1
    funext i
    fin_cases i <;> rfl
  have breaks : TernaryW.column_pairing T.matrix A.matrix A.matrix ≠ 0 :=
    binary_outside_breaks A.matrix T.matrix opposite c hc line
      (by rwa [←binaryForm])
  let pin0 : OrdinaryNegativeCubicGadgets.Macro S.source.H 1 :=
    ⟨S.source.zeroPin.network,S.source.zeroPin.labels,S.source.zeroPin.exact,S.source.zeroPin.ordinary⟩
  have pin : pin0.network.denote=fun x => S.source.scalar*
      Holant.LocalDrafts.MainChain.QuaternaryUnaryAccess.pin false x := by
    funext x
    have hx : (fun _ : Fin 1 => x 0)=x := by
      funext i
      exact congrArg x (Fin.eq_zero i).symm
    rw [←hx]
    cases h : x 0
    · simpa [h,Holant.LocalDrafts.MainChain.QuaternaryUnaryAccess.pin] using S.source.zeroPinFalse
    · simpa [h,Holant.LocalDrafts.MainChain.QuaternaryUnaryAccess.pin] using S.source.zeroPinTrue
  exact TernaryW.binary_break_isotropic_hard S.source.K S.source.F S.source.H L S.source.back
    P PG PR PF PN S.source.negative N pin0 S.source.scalar S.source.scalarNonzero pin
    binary A B C T form bc ab ca binaryForm breaks

/-- The W whole-family selector genuinely closes its binary exit. Its sole
remaining factor-selection arm is a physical prime of arity at least three
outside a chosen matching orientation, in the exact same source table. -/
theorem residual_hard_or_outside_large_prime {L : Paper2.ExactInput.Language}
    (S : IsotropicWSource L)
    (P : SourceFaithful.Paper1Accepted) (PG : SourceFaithful.Paper1DirectGadgetAccepted)
    (PR : SourceFaithful.Paper1RestrictionAccepted) (PF : SourceFaithful.Paper1FactorClosureAccepted)
    (PN : SourceFaithful.Paper1NormalizationAccepted) :
    Paper2.FixedFieldOutput.SharpPHard .ordinary L ∨
      ∃ opposite : Bool, ∃ n, 3 ≤ n ∧ ∃ V : NoXOrdinaryGraphAdjoin.Output S.source.H n,
        Prime (⟨n,V.network.denote⟩ : Holant.AnySignature S.source.K) ∧
        ¬ matchingImage opposite n
          (RingHomRealization.mapSignature S.source.K.subtype V.network.denote) := by
  classical
  obtain ⟨N,A,B,C,form,bc,ab,ca⟩ := S.residual
  obtain ⟨h0,_,iso,_⟩ := TernaryW.common_isotropic_line A B C bc ab ca
  obtain ⟨opposite,c,hc,line⟩ := isotropic_orientation A.matrix h0 iso
  obtain ⟨n,big,V,pv,outside⟩ := residual_outside_prime_graph S opposite
  by_cases hn : n=2
  · subst n
    exact Or.inl (outside_binary_hard S P PG PR PF PN N A B C form bc ab ca
      opposite c hc line V pv outside)
  · exact Or.inr ⟨opposite,n,by omega,V,pv,outside⟩

end
end Paper2.Paper1Proved.OddUnary.WEscape
