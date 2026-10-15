import Holant.Proofs.Dichotomy.Ordinary.OrdinaryTargetInterpolationPhysical
import Paper2.Paper1ProvedOddUnaryJordanTargetMachine
import Paper2.Complexity.Interpolation.TargetWeightsCorrectness
import Holant.Proofs.BinaryInterpolation.OriginalTables

/-! Finite-target recovery from the exact emitted path records, with the
same fixed field and serialized occurrence count as the actual machine. -/
noncomputable section
namespace Paper2.Paper1Proved.OddUnary.JordanTargetRecovery
open Holant Holant.Algebraic Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.BinaryInterpolation Holant.Complexity.BinaryInterpolation.Chains
open Holant.LocalDrafts.BinaryInterpolation
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.Certificates.MatchingContractionClosure
namespace M
export JordanTargetMachine (Data Input inputEncoding queryEncoding values interpolatedValue controlled)
end M
namespace P
export OrdinaryTargetInterpolationPhysical (query_partition)
end P
namespace W
export Paper2.Complexity.Interpolation.TargetWeights (value_polynomial)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K] {n s b : ℕ} {arity : ℕ→ℕ}
variable {field : FixedField K n} {T : ExactSignatureTables n s b arity} (d : M.Data field T)
abbrev G := fun i x=>field.decode (T.vertex i x)
abbrev kernels := fun i a b=>field.decode (T.edge i a b)
abbrev S := OriginalTables.tables d.template d.valid (G (field:=field) (T:=T)) (kernels (field:=field) (T:=T))
abbrev slot (B : Binary (K:=K)) :=
  OriginalTables.binarySlot d.template d.valid (G (field:=field) (T:=T)) (kernels (field:=field) (T:=T)) d.binary B
variable (C H : Binary (K:=K))
def value (r : M.Input d) : K :=
  (r.val.realize r.property
    (RawPolynomial.pencil (S d) (slot d C) (slot d H) s d.target)
    (kernels (field:=field) (T:=T))).denote Fin.elim0
variable (hchain : ∀ k : ℕ,
    ((explicitTemplate s d.edge.val k).network
      (explicitTemplate_wellFormed (PhysicalQueries.A (s:=s) arity d.template) PhysicalQueries.newLabel
        (PhysicalQueries.new_arity (s:=s) arity d.template d.binary) d.edge k)
      (S d) (kernels (field:=field) (T:=T))).denote =
      binarySignature (d.gamma^(k+1) • (C+((k+1:ℕ):K) • H)))

include hchain in
theorem sample (r : M.Input d) (i : Fin (occurrences s r.val+1)) :
    M.values d r i=d.gamma^((i.val+1)*occurrences s r.val)*
      (RawPolynomial.polynomial r.val r.property (S d) (slot d C) (slot d H)
        (kernels (field:=field) (T:=T)) s).eval (((i.val+1:ℕ):K)) := by
  rw [M.values, ExactSignatureTables.evaluate_eq_decoded]
  have hp := P.query_partition arity d.template d.valid d.binary d.edge
    (S d) (slot d C) (slot d H) (G (field:=field) (T:=T)) (kernels (field:=field) (T:=T)) C H
    d.gamma (fun t=>(t:K))
    (OriginalTables.binarySlot_new d.template d.valid (G (field:=field) (T:=T)) (kernels (field:=field) (T:=T)) d.binary C)
    (OriginalTables.binarySlot_new d.template d.valid (G (field:=field) (T:=T)) (kernels (field:=field) (T:=T)) d.binary H)
    hchain 1 (OriginalTables.tables_local d.template d.valid (G (field:=field) (T:=T)) (kernels (field:=field) (T:=T))) ⟨r,i⟩
  simpa only [one_mul] using hp

include hchain in
theorem recovery (hg : d.gamma≠0) (r : M.Input d) :
    M.interpolatedValue d r=value d C H r := by
  change Paper2.Complexity.Interpolation.TargetWeights.value d.gamma d.target
    (occurrences s r.val) (M.values d r)=_
  have he : M.values d r=fun i => d.gamma^((i.val+1)*occurrences s r.val)*
      (RawPolynomial.polynomial r.val r.property (S d) (slot d C) (slot d H)
        (kernels (field:=field) (T:=T)) s).eval (((i.val+1:ℕ):K)) :=
    funext (sample d C H hchain r)
  rw [he]
  have hr := W.value_polynomial d.gamma d.target hg (occurrences s r.val)
    (RawPolynomial.polynomial r.val r.property (S d) (slot d C) (slot d H)
      (kernels (field:=field) (T:=T)) s)
    (RawPolynomial.polynomial_degree r.val r.property (S d) (slot d C) (slot d H)
      (kernels (field:=field) (T:=T)) s)
  exact hr.trans (RawPolynomial.polynomial_eval _ _ _ _ _ _ _ _)

/-- All hypotheses before this reduction are fixed local path semantics,
never a supplied closed-instance reduction or classification backend. -/
def controlled (hg : d.gamma≠0) :
    LengthControlledOracleReduction (M.inputEncoding d) field.encoding
      (M.queryEncoding (s:=s) (b:=b) (arity:=arity)) field.encoding
      (value d C H) (T.evaluate field) := by
  have eqn : M.interpolatedValue d=value d C H := funext (recovery d C H hchain hg)
  rw [←eqn]
  exact M.controlled d

end Paper2.Paper1Proved.OddUnary.JordanTargetRecovery
end
