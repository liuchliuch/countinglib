import Paper2.Paper1ProvedOddUnaryJordanBinaryInterpolation
import Holant.Proofs.BinaryInterpolation.MachineCapstone
import Holant.Proofs.Algorithms.TraceQueryControl

/-! The top Jordan direction is recovered by the retained arithmetic-node
coefficient machine. The endpoint retains the actual successful query trace
and derives its safety from those emitted original-alphabet records. -/
namespace Paper2.Paper1Proved.OddUnary.JordanTopFamily
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution Holant.Complexity.BinaryInterpolation
open Holant.Complexity.BinaryInterpolation.Chains
open Holant.LocalDrafts.BinaryInterpolation
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.MainChain
open Holant.Certificates.MatchingContractionClosure
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {r degree : ℕ} {a : ℕ → ℕ}
variable (F : FixedField K degree) (H : (i : Fin r) → Holant.Signature K (a i.val))
variable {phi : K →+* AlgebraicComplex} (J : NRCanonical.JordanReceipt (H:=H) phi)
namespace B
export JordanBinaryInterpolation (base template direction)
end B

def data : MachineCapstone.Data F (B.base F H) where
  template := B.template H J
  valid := J.graph.labels.wellFormed
  binary := rfl
  edge := 0
  gamma := J.eigenvalueK
  rho := 0
  geometric := false

abbrev arity := PhysicalQueries.A (s:=r) a (B.template H J)
abbrev signatures := OriginalTables.binarySlot (B.template H J) J.graph.labels.wellFormed H
  (fun _ : Fin 1=>Signature.equality) rfl (B.direction H J)
def tables : ExactSignatureTables degree (r+1) 1 (arity H J) where
  vertex i x := F.decode.symm (signatures H J i x)
  edge _ b c := F.decode.symm (Signature.equality b c)

/-- The samples are the same original-family queries as finite target recovery. -/
theorem sample (injective : Function.Injective phi)
    (q : MachineCapstone.Input (data F H J)) (i : Fin (occurrences r q.val+1)) :
    MachineCapstone.values (data F H J) q i=J.eigenvalueK^((i.val+1)*occurrences r q.val)*
      (RawPolynomial.polynomial q.val q.property
        (JordanTargetRecovery.S (JordanBinaryInterpolation.data F H J 0))
        (JordanTargetRecovery.slot (JordanBinaryInterpolation.data F H J 0) 1)
        (JordanTargetRecovery.slot (JordanBinaryInterpolation.data F H J 0) (B.direction H J))
        (fun _ : Fin 1=>Signature.equality) r).eval ((i.val+1:ℕ):K) := by
  have hk : JordanTargetRecovery.kernels (field:=F) (T:=B.base F H)=
      (fun _ : Fin 1=>Signature.equality) := by
    funext e b c
    exact F.decode.apply_symm_apply (Signature.equality b c)
  have he := JordanTargetRecovery.sample (JordanBinaryInterpolation.data F H J 0)
      1 (B.direction H J) (JordanBinaryInterpolation.chain F H J injective 0) q i
  rw [hk] at he
  simpa only [B.base,NoXOrdinaryGraphAdjoin.baseTables,
    QuaternaryOrdinaryCompanion.tables,LinearEquiv.apply_symm_apply,
    JordanTargetMachine.values,MachineCapstone.values,data,JordanBinaryInterpolation.data]
    using he

theorem recovery (injective : Function.Injective phi)
    (q : MachineCapstone.Input (data F H J)) :
    MachineCapstone.interpolatedValue (data F H J) q=(tables F H J).evaluate F q := by
  let d := JordanBinaryInterpolation.data F H J 0
  let nodes : Fin (occurrences r q.val+1)→K := fun i=>((i.val+1:ℕ):K)
  let scales : Fin (occurrences r q.val+1)→K := fun i=>J.eigenvalueK^(i.val+1)
  have hi : Function.Injective nodes := positive_natural_nodes_injective _
  have hs : ∀i,scales i≠0 := fun _=>pow_ne_zero _ J.eigenvalueK_nonzero
  change commonNumerator (queryDenominator nodes scales) (MachineCapstone.values (data F H J) q)/
      commonDenominator (queryDenominator nodes scales)=_
  rw [←recover_normalized_common nodes scales _ hi hs]
  have he : (fun i=>MachineCapstone.values (data F H J) q i/(scales i)^occurrences r q.val)=
      (fun i=>(RawPolynomial.polynomial q.val q.property (JordanTargetRecovery.S d)
        (JordanTargetRecovery.slot d 1) (JordanTargetRecovery.slot d (B.direction H J))
        (fun _ : Fin 1=>Signature.equality) r).eval (nodes i)) := by
    funext i
    rw [sample F H J injective q i]
    simp only [scales,←pow_mul]
    exact mul_div_cancel_left₀ _ (pow_ne_zero _ J.eigenvalueK_nonzero)
  rw [he,recoverTop_eq_coefficient _ hi _ (RawPolynomial.polynomial_degree _ _ _ _ _ _ _),
    RawPolynomial.polynomial_top]
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [tables,LinearEquiv.apply_symm_apply]
  have hr := OriginalTables.right_eq_binarySlot (B.template H J) J.graph.labels.wellFormed
    H (fun _ : Fin 1=>Signature.equality) rfl (B.direction H J)
  have hg : JordanTargetRecovery.G (field:=F) (T:=B.base F H)=H := by
    funext i x
    exact F.decode.apply_symm_apply (H i x)
  have hk : JordanTargetRecovery.kernels (field:=F) (T:=B.base F H)=
      (fun _ : Fin 1=>Signature.equality) := by
    funext e b c
    exact F.decode.apply_symm_apply (Signature.equality b c)
  simpa only [d,JordanTargetRecovery.S,JordanTargetRecovery.slot,JordanBinaryInterpolation.data,
    hg,hk,hr,signatures]

/-- Attach query control to the already checked retained top-coefficient
machine, using its actual same-run transcript. -/
def machineControlled : LengthControlledOracleReduction
    (MachineCapstone.inputEncoding (data F H J)) F.encoding
    (RawClosedNetwork.validatedEncoding r 1 a) F.encoding
    (MachineCapstone.interpolatedValue (data F H J)) ((B.base F H).evaluate F) where
  reduction := MachineCapstone.reduction (data F H J)
  targetOutput := (B.base F H).outputBound F
  queryBound := (EncodedBatch.queriesComputes a (B.template H J) J.graph.labels.wellFormed rfl (0:Fin 1)).outputBound.bound
  safeQuery oracle ho q t cfg run query := by
    obtain ⟨_,_,trace⟩ := MachineCapstone.execution (data F H J) oracle ho q
    have member := Holant.LocalDrafts.MainChain.TraceQueryControl.transcript_member trace t cfg run query
    obtain ⟨v,hv,eqn⟩ := List.mem_map.mp member
    refine ⟨v,eqn.symm,?_⟩
    change (cfg.stk (MachineCapstone.machine (data F H J)).queryStack).length≤_
    rw [eqn.symm]
    have hm := OracleBatch.member_length_le
      ((MachineCapstone.queries (data F H J) q).map (RawClosedNetwork.validatedEncoding r 1 a).encode)
      ((RawClosedNetwork.validatedEncoding r 1 a).encode v)
      (List.mem_map.mpr ⟨v,hv,rfl⟩)
    have hb := (EncodedBatch.queriesComputes a (B.template H J) J.graph.labels.wellFormed rfl
      (0:Fin 1)).outputBound.length_le q
    rw [OracleBatch.list_encode] at hb
    exact hm.trans hb

omit [CharZero K] in
theorem ordinary_tables : QuaternaryOrdinaryCompanion.tables F (signatures H J)=tables F H J := rfl

def controlled (injective : Function.Injective phi) :
    LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding (r+1) 1 (arity H J)) F.encoding
      (RawClosedNetwork.validatedEncoding r 1 a) F.encoding
      ((QuaternaryOrdinaryCompanion.tables F (signatures H J)).evaluate F)
      ((B.base F H).evaluate F) := by
  rw [ordinary_tables]
  have he : MachineCapstone.interpolatedValue (data F H J)=(tables F H J).evaluate F :=
    funext (recovery F H J injective)
  rw [←he]
  exact machineControlled F H J

omit [Algebra ℚ K] [CharZero K] in
theorem old_literal (i : Fin r) :
    (⟨arity H J (Fin.castAdd 1 i).val,signatures H J (Fin.castAdd 1 i)⟩ : Holant.AnySignature K)=
      ⟨a i.val,H i⟩ := OriginalTables.binarySlot_old _ _ _ _ _ _ i

omit [Algebra ℚ K] [CharZero K] in
theorem new_literal :
    (⟨arity H J r,signatures H J ⟨r,Nat.lt_succ_self r⟩⟩ : Holant.AnySignature K)=
      ⟨2,Holant.Complexity.BinaryInterpolation.Chains.binarySignature (B.direction H J)⟩ :=
  OriginalTables.binarySlot_new _ _ _ _ _ _

end
end Paper2.Paper1Proved.OddUnary.JordanTopFamily
