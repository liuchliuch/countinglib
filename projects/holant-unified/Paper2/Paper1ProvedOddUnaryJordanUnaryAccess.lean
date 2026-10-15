import Paper2.Paper1ProvedOddUnaryJordanInterpolationSemantics
import Paper2.Paper1ProvedOddUnaryJordanTopFamily
import Paper2.Paper1ProvedOddUnaryJordanScaledGraphAdjoin
import Paper2.Paper1ProvedOddUnaryRetainedTable

/-! Same-field unary access from a genuine ordinary Jordan graph and a
nonzero scalar zero pin. Each finite extension has an executed, length-
controlled reduction to the original table and retains its old literal rows. -/
namespace Paper2.Paper1Proved.OddUnary.JordanUnaryAccess
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution Holant.Complexity.BinaryInterpolation
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
open scoped Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {r degree : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin r)→Holant.Signature K (a i.val))

/-- The extra rows are literal original-field signatures. Old graphs can be
relabeled through `old`, while the checked `back` evaluates all new rows. -/
structure Extension (v : Bool→K) where
  count : ℕ
  arity : ℕ→ℕ
  signatures : (i : Fin count)→Holant.Signature K (arity i.val)
  old : Fin r→Fin count
  old_literal : ∀i,(⟨arity (old i).val,signatures (old i)⟩ : Holant.AnySignature K)=⟨a i.val,H i⟩
  label : Fin count
  unary_literal : (⟨arity label.val,signatures label⟩ : Holant.AnySignature K)=⟨1,fun x=>v (x 0)⟩
  back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) F.encoding
    (RawClosedNetwork.validatedEncoding r 1 a) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F signatures).evaluate F)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)

section Cap
variable {s : ℕ} {b : ℕ→ℕ}
variable (T : (i : Fin s)→Holant.Signature K (b i.val))
variable (old : Fin r→Fin s)
variable (literal : ∀i,(⟨b (old i).val,T (old i)⟩ : Holant.AnySignature K)=⟨a i.val,H i⟩)
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding s 1 b) F.encoding
    (RawClosedNetwork.validatedEncoding r 1 a) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F T).evaluate F)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F))
variable (P : Macro H 1) (c : K)
variable (hp : P.network.denote=fun x=>NRJordanPowers.pin c (x 0))
variable (j : Fin s) (B : Matrix Bool Bool K)
variable (hb : (⟨b j.val,T j⟩ : Holant.AnySignature K)=⟨2,JordanChain.binarySignature B⟩)

abbrev capMacro := JordanChain.applyPin (Macro.row j (JordanChain.binarySignature B) hb)
  (RetainedTable.liftMacro old literal P)

def capOutput : NoXOrdinaryGraphAdjoin.Output T 1 where
  network := (capMacro H T old literal P j B hb).network
  labels := (capMacro H T old literal P j B hb).labels
  exact := (capMacro H T old literal P j B hb).exact
  ordinary := (capMacro H T old literal P j B hb).edges

include hp in
theorem capOutput_denote : (capOutput H T old literal P j B hb).network.denote=
    fun x=>(B *ᵥ NRJordanPowers.pin c) (x 0) :=
  JordanChain.applyPin_denote _ _ _ _ (Macro.row_denote _ _ _) hp

/-- Fixed cap substitution and fixed scalar-power correction are both actual
programs; the assumed data here are local matrix and row identities only. -/
def capExtension (v : Bool→K) (q : K) (hq : q≠0)
    (hv : B *ᵥ NRJordanPowers.pin c=fun bit=>q*v bit) : Extension F H v where
  count := s+1
  arity := JordanScaledGraphAdjoin.arity T (capOutput H T old literal P j B hb)
  signatures := JordanScaledGraphAdjoin.signatures F T (capOutput H T old literal P j B hb) q
  old i := Fin.castAdd 1 (old i)
  old_literal i := (JordanScaledGraphAdjoin.old_literal F T
    (capOutput H T old literal P j B hb) q (old i)).trans (literal i)
  label := ⟨s,Nat.lt_succ_self s⟩
  unary_literal := by
    apply (JordanScaledGraphAdjoin.new_literal F T
      (capOutput H T old literal P j B hb) q).trans
    apply congrArg (fun f : Holant.Signature K 1=>(⟨1,f⟩ : Holant.AnySignature K))
    funext x
    rw [capOutput_denote H T old literal P c hp j B hb,hv]
    exact mul_div_cancel_left₀ _ hq
  back := Programme.compose
    (JordanScaledGraphAdjoin.source F T (capOutput H T old literal P j B hb) q hq) back

end Cap
section Jordan
variable {phi : K→+* AlgebraicComplex} (J : NRCanonical.JordanReceipt (H:=H) phi)
variable (injective : Function.Injective phi) (P : Macro H 1) (c : K) (hc : c≠0)
variable (hp : P.network.denote=fun x=>NRJordanPowers.pin c (x 0))


include injective in
theorem finite_cap (v : Bool→K) (ha : JordanInterpolation.leftCoefficient J v≠0) :
    JordanBinaryInterpolation.pencil H J (JordanInterpolation.rightCoefficient J v/JordanInterpolation.leftCoefficient J v) *ᵥ
        NRJordanPowers.pin c=
      fun bit=>(c/(JordanInterpolation.leftCoefficient J v*J.eigenvalueK))*v bit := by
  have hf := JordanInterpolation.unary_pencil J injective v ha
  funext bit
  have hv := congrFun hf (fun _ : Fin 1=>bit)
  rw [hv]
  cases bit <;>
    simp only [JordanBinaryInterpolation.pencil,JordanBinaryInterpolation.direction,
      Matrix.mulVec,dotProduct,Fintype.sum_bool,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,
      NRJordanPowers.nilpotent,Matrix.vecMulVec_apply,NRJordanPowers.pin,NRJordanPowers.repeated,
      Matrix.one_apply,Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false,
      mul_zero,zero_add,one_mul,mul_one] at ⊢
  all_goals simp only [JordanChain.left,JordanChain.right,ite_true,ite_false,Bool.false_eq_true]
  all_goals field_simp [ha,J.eigenvalueK_nonzero]
  all_goals ring

/-- Every nonzero unary in the original field has actual finite table access.
The affine and top-direction cases use different proved interpolation programs. -/
def extension (v : Bool→K) (hv : v≠0) : Extension F H v := by
  classical
  by_cases ha : JordanInterpolation.leftCoefficient J v=0
  · have hb : JordanInterpolation.rightCoefficient J v≠0 := by
      intro hb
      apply hv
      have he := JordanInterpolation.unary_top J injective v ha
      funext bit
      have h := congrFun he (fun _ : Fin 1=>bit)
      simpa only [hb,zero_mul,Pi.zero_apply] using h
    let T := JordanTopFamily.signatures H J
    let old : Fin r→Fin (r+1) := Fin.castAdd 1
    let q := c/(J.eigenvalueK*JordanInterpolation.rightCoefficient J v)
    have hq : q≠0 := div_ne_zero hc (mul_ne_zero J.eigenvalueK_nonzero hb)
    apply capExtension F H T old (JordanTopFamily.old_literal H J)
      (JordanTopFamily.controlled F H J injective) P c hp
      ⟨r,Nat.lt_succ_self r⟩ (JordanBinaryInterpolation.direction H J)
      (JordanTopFamily.new_literal H J) v q hq
    have he := JordanInterpolation.unary_top J injective v ha
    funext bit
    have h := congrFun he (fun _ : Fin 1=>bit)
    rw [JordanBinaryInterpolation.direction,Matrix.smul_mulVec,NRJordanPowers.nilpotent_pin_image]
    simp only [Pi.smul_apply,smul_eq_mul] at ⊢
    simp only [JordanChain.right] at h
    change (J.defectK/J.eigenvalueK)*(c*NRJordanPowers.repeated J.ratioK bit)=q*v bit
    rw [h]
    cases bit <;> simp only [NRJordanPowers.repeated,Bool.false_eq_true,ite_true,ite_false,q]
    all_goals field_simp [J.eigenvalueK_nonzero,hb]
    all_goals ring
  · let z := JordanInterpolation.rightCoefficient J v/JordanInterpolation.leftCoefficient J v
    let T := JordanBinaryInterpolation.signatures F H J z
    let old : Fin r→Fin (r+1) := Fin.castAdd 1
    let q := c/(JordanInterpolation.leftCoefficient J v*J.eigenvalueK)
    have hq : q≠0 := div_ne_zero hc (mul_ne_zero ha J.eigenvalueK_nonzero)
    exact capExtension F H T old (JordanBinaryInterpolation.old_literal F H J z)
      (JordanBinaryInterpolation.controlled F H J injective z) P c hp
      ⟨r,Nat.lt_succ_self r⟩ (JordanBinaryInterpolation.pencil H J z)
      (JordanBinaryInterpolation.new_literal F H J z) v q hq
      (finite_cap H J injective c v ha)

end Jordan
end
end Paper2.Paper1Proved.OddUnary.JordanUnaryAccess
