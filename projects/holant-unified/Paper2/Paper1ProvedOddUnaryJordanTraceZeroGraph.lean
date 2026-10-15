import Paper2.Paper1ProvedOddUnaryJordanBreaklineSymmetric
import Paper2.Paper1ProvedOddUnaryJordanBinaryInterpolation
import Paper2.Paper1ProvedOddUnaryJordanUnaryFamily
import Paper2.Paper1ProvedOddUnaryTernarySymmetricWGraph

/-! Physical equality-edge Gram and Jordan-congruence graphs realizing
the literal symmetric trace-zero exit. The interpolated pencil table has
an executed controlled reduction to the unchanged original table. -/
namespace Paper2.Paper1Proved.OddUnary.JordanTraceZeroGraph
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution Holant.Complexity.BinaryCompose
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
open scoped Matrix BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
variable {K : Type} [Field K] {r : ℕ} {a : ℕ→ℕ}
variable {H : (i : Fin r)→Holant.Signature K (a i.val)}

def matrix (Q : NoXOrdinaryGraphAdjoin.Output H 2) : Matrix Bool Bool K:=
  fun b d=>Q.network.denote ![b,d]

def ofOutput (Q : NoXOrdinaryGraphAdjoin.Output H 2) : Macro H 2:=
  ⟨Q.network,Q.labels,Q.exact,Q.ordinary⟩

theorem macro_denote (Q : NoXOrdinaryGraphAdjoin.Output H 2) :
    (ofOutput Q).network.denote=JordanChain.binarySignature (matrix Q) := by
  funext x
  change Q.network.denote x=Q.network.denote ![x 0,x 1]
  congr 1
  funext i
  fin_cases i <;> rfl

theorem transpose_denote (M : Macro H 2) (T : Matrix Bool Bool K)
    (form : M.network.denote=JordanChain.binarySignature T) :
    (TernaryW.transposeMacro M).network.denote=JordanChain.binarySignature T.transpose := by
  rw [TernaryW.transposeMacro,Macro.reindex_denote,form]
  funext x
  rfl

def gram (M : Macro H 2) (left : Bool) : Macro H 2:=
  if left then JordanChain.series (TernaryW.transposeMacro M) M
  else JordanChain.series M (TernaryW.transposeMacro M)

theorem gram_denote (M : Macro H 2) (T : Matrix Bool Bool K)
    (form : M.network.denote=JordanChain.binarySignature T) (left : Bool) :
    (gram M left).network.denote=JordanChain.binarySignature
      (if left then JordanBreaklineSymmetric.gramLeft T else JordanBreaklineSymmetric.gramRight T) := by
  cases left
  · exact JordanChain.series_denote M (TernaryW.transposeMacro M) T T.transpose form
      (transpose_denote M T form)
  · exact JordanChain.series_denote (TernaryW.transposeMacro M) M T.transpose T
      (transpose_denote M T form) form

theorem product_congruence (P S : Matrix Bool Bool K) :
    (P.transpose*S)*P=JordanBreaklineSymmetric.congruence P S := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,JordanBreaklineSymmetric.congruence,
    Finset.sum_mul]
  rw [Finset.sum_comm]

def congruence (P S : Macro H 2) : Macro H 2:=
  JordanChain.series (JordanChain.series (TernaryW.transposeMacro P) S) P

theorem congruence_denote (P S : Macro H 2) (B D : Matrix Bool Bool K)
    (hp : P.network.denote=JordanChain.binarySignature B)
    (hs : S.network.denote=JordanChain.binarySignature D) :
    (congruence P S).network.denote=JordanChain.binarySignature
      (JordanBreaklineSymmetric.congruence B D) := by
  rw [congruence,JordanChain.series_denote _ _ _ _
    (JordanChain.series_denote _ _ _ _ (transpose_denote P B hp) hs) hp,
    product_congruence]

variable [Algebra ℚ K] [CharZero K] {degree : ℕ}
variable (F : FixedField K degree)

structure Extension where
  count : ℕ
  arity : ℕ→ℕ
  signatures : (i : Fin count)→Holant.Signature K (arity i.val)
  old : Fin r→Fin count
  old_literal : ∀i,(⟨arity (old i).val,signatures (old i)⟩ : Holant.AnySignature K)=⟨a i.val,H i⟩
  graph : NoXOrdinaryGraphAdjoin.Output signatures 2
  tracezero : JordanBreaklineSymmetric.trace (matrix graph)=0
  symmetric : ∀i j,matrix graph i j=matrix graph j i
  nonsingular : OneHotBinaryProjection.determinant (matrix graph)≠0
  back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) F.encoding
    (RawClosedNetwork.validatedEncoding r 1 a) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F signatures).evaluate F)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)

variable {phi : K→+* AlgebraicComplex}
variable (J : NRCanonical.JordanReceipt (H:=H) phi)

theorem interpolated_pencil (z : K) :
    JordanBinaryInterpolation.pencil H J (z/(J.defectK/J.eigenvalueK))=
      JordanBreaklineSymmetric.pencil J.ratioK z := by
  ext i j
  simp only [JordanBinaryInterpolation.pencil,JordanBinaryInterpolation.direction,
    Matrix.add_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul,
    NRJordanPowers.nilpotent,Matrix.vecMulVec_apply,JordanBreaklineSymmetric.pencil]
  field_simp [J.defectK_nonzero,J.eigenvalueK_nonzero]

theorem extension_exists (injective : Function.Injective phi)
    (Q : NoXOrdinaryGraphAdjoin.Output H 2)
    (det : OneHotBinaryProjection.determinant (matrix Q)≠0)
    (live : OneHotLineProjection.line (NRJordanPowers.repeated J.ratioK) (matrix Q)≠0) :
    Nonempty (Extension (H:=H) F) := by
  classical
  rcases JordanBreaklineSymmetric.tracezero_recipe J.ratioK (J.ratioK_square injective)
      (matrix Q) live with direct|⟨left,z,trace,symmetric,determinant⟩
  · exact ⟨{
      count:=r
      arity:=a
      signatures:=H
      old:=id
      old_literal:=fun _=>rfl
      graph:=Q
      tracezero:=direct.1
      symmetric:=direct.2
      nonsingular:=det
      back:=controlledOneQueryOfEq (identityComputes (RawClosedNetwork.validatedEncoding r 1 a))
        (identityComputes F.encoding) ((QuaternaryOrdinaryCompanion.tables F H).outputBound F)
        ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (fun _=>rfl) }⟩
  · let w:=z/(J.defectK/J.eigenvalueK)
    let T:=JordanBinaryInterpolation.signatures F H J w
    let old:Fin r→Fin (r+1):=Fin.castAdd 1
    have oldeq:=JordanBinaryInterpolation.old_literal F H J w
    let M:=RetainedTable.liftMacro old oldeq (ofOutput Q)
    let S:=gram M left
    have hs : S.network.denote=JordanChain.binarySignature
        (if left then JordanBreaklineSymmetric.gramLeft (matrix Q)
          else JordanBreaklineSymmetric.gramRight (matrix Q)) :=
      gram_denote M (matrix Q) (macro_denote Q) left
    have literal : (⟨JordanBinaryInterpolation.arity F H J w r,T ⟨r,Nat.lt_succ_self r⟩⟩ :
        Holant.AnySignature K)=⟨2,JordanChain.binarySignature
          (JordanBreaklineSymmetric.pencil J.ratioK z)⟩ := by
      rw [JordanBinaryInterpolation.new_literal,interpolated_pencil J z]
      rfl
    let P:=Macro.row ⟨r,Nat.lt_succ_self r⟩ _ literal
    let C:=congruence P S
    have formC : C.network.denote=JordanChain.binarySignature
        (JordanBreaklineSymmetric.congruence (JordanBreaklineSymmetric.pencil J.ratioK z)
          (if left then JordanBreaklineSymmetric.gramLeft (matrix Q)
            else JordanBreaklineSymmetric.gramRight (matrix Q))) :=
      congruence_denote P S _ _ (Macro.row_denote _ _ literal) hs
    let R : NoXOrdinaryGraphAdjoin.Output T 2:=⟨C.network,C.labels,C.exact,C.edges⟩
    have matrixR : matrix R=JordanBreaklineSymmetric.congruence
        (JordanBreaklineSymmetric.pencil J.ratioK z)
        (if left then JordanBreaklineSymmetric.gramLeft (matrix Q)
          else JordanBreaklineSymmetric.gramRight (matrix Q)) := by
      funext i j
      exact congrFun formC ![i,j]
    exact ⟨{
      count:=r+1
      arity:=JordanBinaryInterpolation.arity F H J w
      signatures:=T
      old:=old
      old_literal:=oldeq
      graph:=R
      tracezero:=by rwa [matrixR]
      symmetric:=by rwa [matrixR]
      nonsingular:=by rw [matrixR,determinant];exact pow_ne_zero 2 det
      back:=JordanBinaryInterpolation.controlled F H J injective w }⟩

end
end Paper2.Paper1Proved.OddUnary.JordanTraceZeroGraph

