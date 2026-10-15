import Paper2.Paper1ProvedOddUnaryNRJordanPowers
import Paper2.Paper1ProvedOddUnaryJordanChain
import Paper2.Paper1ProvedOddUnaryJordanTargetFamily
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationChain

/-! A Jordan graph supplies every fixed finite point of its binary pencil
through actual positive equality-edge chains and the checked target machine.
All coefficients, old rows, and answer bytes stay in the original field. -/
namespace Paper2.Paper1Proved.OddUnary.JordanBinaryInterpolation
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution Holant.Complexity.BinaryInterpolation
open Holant.Complexity.BinaryInterpolation.Chains hiding binarySignature
open Holant.LocalDrafts.BinaryInterpolation
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure
open scoped Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {r degree : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K degree) (H : (i : Fin r) → Holant.Signature K (a i.val))
variable {phi : K →+* AlgebraicComplex} (J : NRCanonical.JordanReceipt (H:=H) phi)

abbrev base := NoXOrdinaryGraphAdjoin.baseTables F H
abbrev template := J.graph.labels.template

def direction : Matrix Bool Bool K :=
  (J.defectK/J.eigenvalueK) • NRJordanPowers.nilpotent J.ratioK

def pencil (z : K) : Matrix Bool Bool K := 1+z • direction H J

def data (z : K) : JordanTargetMachine.Data F (base F H) where
  template := template H J
  valid := J.graph.labels.wellFormed
  binary := rfl
  edge := 0
  gamma := J.eigenvalueK
  target := z

abbrev arity (z : K) := JordanTargetFamily.a (data F H J z)
abbrev signatures (z : K) := JordanTargetFamily.signatures (data F H J z) 1 (direction H J)
abbrev tables (z : K) := JordanTargetFamily.tables (data F H J z) 1 (direction H J)

/-- The runtime compiler uses exactly the recorded ordinary Jordan graph. -/
theorem chain (injective : Function.Injective phi) (z : K) (k : ℕ) :
    ((explicitTemplate r 0 k).network
      (explicitTemplate_wellFormed (PhysicalQueries.A (s:=r) a (template H J)) PhysicalQueries.newLabel
        (PhysicalQueries.new_arity (s:=r) a (template H J) rfl) (0 : Fin 1) k)
      (JordanTargetRecovery.S (data F H J z))
      (JordanTargetRecovery.kernels (field:=F) (T:=base F H))).denote=
      Holant.Complexity.BinaryInterpolation.Chains.binarySignature
        (J.eigenvalueK^(k+1) • (1+((k+1:ℕ):K) • direction H J)) := by
  have hb : (⟨(template H J).boundary,((template H J).network J.graph.labels.wellFormed
      (JordanTargetRecovery.G (field:=F) (T:=base F H))
      (JordanTargetRecovery.kernels (field:=F) (T:=base F H))).denote⟩ : Holant.AnySignature K)=
      ⟨2,Holant.Complexity.BinaryInterpolation.Chains.binarySignature (NRJordanPowers.receiptMatrix J)⟩ := by
    apply congrArg (fun f : Holant.Signature K 2 => (⟨2,f⟩ : Holant.AnySignature K))
    exact (NoXOrdinaryGraphAdjoin.macro_exact F H J.graph).trans (JordanChain.binary_denote J)
  have hc := OrdinaryTargetInterpolationChain.explicitTemplate_denote_I
    (PhysicalQueries.A (s:=r) a (template H J)) PhysicalQueries.newLabel
    (PhysicalQueries.new_arity (s:=r) a (template H J) rfl) (0 : Fin 1) k
    (NRJordanPowers.receiptMatrix J)
    (JordanTargetRecovery.S (data F H J z))
    (JordanTargetRecovery.kernels (field:=F) (T:=base F H))
    ((OriginalTables.tables_new (template H J) J.graph.labels.wellFormed
      (JordanTargetRecovery.G (field:=F) (T:=base F H))
      (JordanTargetRecovery.kernels (field:=F) (T:=base F H))).trans hb)
    (by funext p q; exact F.decode.apply_symm_apply (Signature.equality p q))
  refine hc.trans ?_
  apply congrArg Holant.Complexity.BinaryInterpolation.Chains.binarySignature
  rw [NRJordanPowers.receipt_positive_power J injective k]
  ext i j
  simp only [direction,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,pow_succ]
  field_simp [J.eigenvalueK_nonzero]

theorem old_literal (z : K) (i : Fin r) :
    (⟨arity F H J z (Fin.castAdd 1 i).val,signatures F H J z (Fin.castAdd 1 i)⟩ : Holant.AnySignature K)=
      ⟨a i.val,H i⟩ := by
  have h := JordanTargetFamily.old_literal (data F H J z) 1 (direction H J) i
  apply h.trans
  apply congrArg (fun f : Holant.Signature K (a i.val) => (⟨a i.val,f⟩ : Holant.AnySignature K))
  funext x
  exact F.decode.apply_symm_apply (H i x)

theorem new_literal (z : K) :
    (⟨arity F H J z r,signatures F H J z ⟨r,Nat.lt_succ_self r⟩⟩ : Holant.AnySignature K)=
      ⟨2,Holant.Complexity.BinaryInterpolation.Chains.binarySignature (pencil H J z)⟩ :=
  JordanTargetFamily.new_literal (data F H J z) 1 (direction H J)

omit [CharZero K] in
theorem ordinary_tables (z : K) :
    QuaternaryOrdinaryCompanion.tables F (signatures F H J z)=tables F H J z := rfl

def controlled (injective : Function.Injective phi) (z : K) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (r+1) 1 (arity F H J z)) F.encoding
      (RawClosedNetwork.validatedEncoding r 1 a) F.encoding
      ((QuaternaryOrdinaryCompanion.tables F (signatures F H J z)).evaluate F)
      ((base F H).evaluate F) := by
  rw [ordinary_tables]
  exact JordanTargetFamily.controlled (data F H J z) 1 (direction H J)
    (chain F H J injective z) J.eigenvalueK_nonzero

end
end Paper2.Paper1Proved.OddUnary.JordanBinaryInterpolation
