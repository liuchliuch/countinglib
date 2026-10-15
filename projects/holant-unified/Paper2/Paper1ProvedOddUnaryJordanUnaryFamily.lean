import Paper2.Paper1ProvedOddUnaryJordanUnaryAccess
import Paper2.Paper1ProvedOddUnaryNRWComplete

/-! Finitely many fixed original-field unaries can be adjoined together.
Actual Jordan and pin graphs are retained through every finite step; the
controlled programme is the composition of the checked unary programmes. -/
namespace Paper2.Paper1Proved.OddUnary.JordanUnaryAccess
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution Holant.Complexity.BinaryCompose
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {r degree : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin r)→Holant.Signature K (a i.val))
variable {phi : K→+* AlgebraicComplex}

/-- Retention changes only graph labels; the original-field entries and
Jordan receipt form are literally the same. -/
def retainReceipt {s : ℕ} {b : ℕ→ℕ}
    (T : (i : Fin s)→Holant.Signature K (b i.val))
    (old : Fin r→Fin s)
    (literal : ∀i,(⟨b (old i).val,T (old i)⟩ : Holant.AnySignature K)=⟨a i.val,H i⟩)
    (J : NRCanonical.JordanReceipt (H:=H) phi) : NRCanonical.JordanReceipt (H:=T) phi where
  graph := RetainedTable.lift old literal J.graph
  repeated := J.repeated
  repeatedFalseNonzero := J.repeatedFalseNonzero
  isotropic := J.isotropic
  eigenvalue := J.eigenvalue
  defect := J.defect
  eigenvalueNonzero := J.eigenvalueNonzero
  defectNonzero := J.defectNonzero
  form := J.form
  determinantNonzero := J.determinantNonzero

structure FamilyExtension (V : List (Bool→K)) where
  count : ℕ
  arity : ℕ→ℕ
  signatures : (i : Fin count)→Holant.Signature K (arity i.val)
  old : Fin r→Fin count
  old_literal : ∀i,(⟨arity (old i).val,signatures (old i)⟩ : Holant.AnySignature K)=⟨a i.val,H i⟩
  unary_literal : ∀v∈V,∃j:Fin count,
    (⟨arity j.val,signatures j⟩ : Holant.AnySignature K)=⟨1,fun x=>v (x 0)⟩
  back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) F.encoding
    (RawClosedNetwork.validatedEncoding r 1 a) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F signatures).evaluate F)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)

variable (J : NRCanonical.JordanReceipt (H:=H) phi)
variable (injective : Function.Injective phi) (P : Macro H 1) (c : K) (hc : c≠0)
variable (hp : P.network.denote=fun x=>NRJordanPowers.pin c (x 0))

/-- A fixed finite list incurs only finitely many compositions, each with an
actual finite machine, polynomial clock and same-query safety theorem. -/
def familyExtension : (V : List (Bool→K))→(∀v∈V,v≠0)→FamilyExtension F H V
  | [], _ => {
    count := r
    arity := a
    signatures := H
    old := id
    old_literal := fun _=>rfl
    unary_literal := by intros v hv; exact False.elim (List.not_mem_nil hv)
    back := controlledOneQueryOfEq
      (identityComputes (RawClosedNetwork.validatedEncoding r 1 a))
      (identityComputes F.encoding) ((QuaternaryOrdinaryCompanion.tables F H).outputBound F)
      ((QuaternaryOrdinaryCompanion.tables F H).evaluate F) (fun _=>rfl) }
  | v::V, nonzero => by
    let tail := familyExtension V (fun w hw=>nonzero w (List.mem_cons_of_mem v hw))
    let J' := retainReceipt H tail.signatures tail.old tail.old_literal J
    let P' := RetainedTable.liftMacro tail.old tail.old_literal P
    let head := extension F tail.signatures J' injective P' c hc hp v
      (nonzero v (List.mem_cons_self))
    exact {
      count := head.count
      arity := head.arity
      signatures := head.signatures
      old := head.old ∘ tail.old
      old_literal := fun i=>(head.old_literal (tail.old i)).trans (tail.old_literal i)
      unary_literal := by
        intro w hw
        rcases List.mem_cons.mp hw with equal|member
        · subst w; exact ⟨head.label,head.unary_literal⟩
        · obtain ⟨j,hj⟩ := tail.unary_literal w member
          exact ⟨head.old j,(head.old_literal j).trans hj⟩
      back := Programme.compose head.back tail.back }

end
end Paper2.Paper1Proved.OddUnary.JordanUnaryAccess

namespace Paper2.Paper1Proved.OddUnary.IsotropicWSource
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {L : Paper2.ExactInput.Language} (S : IsotropicWSource L)

/-- There is no interpolator or unary-provider premise: the original W
source supplies its actual Jordan graph and scalar pin internally. -/
theorem unary_extension (v : Bool→S.source.K) (hv : v≠0) :
    letI : Algebra ℚ S.source.K := S.source.K.algebra'
    Nonempty (JordanUnaryAccess.Extension S.source.F S.source.H v) := by
  letI : Algebra ℚ S.source.K := S.source.K.algebra'
  obtain ⟨J⟩ := S.jordan_receipt
  let P : Macro S.source.H 1 :=
    ⟨S.source.zeroPin.network,S.source.zeroPin.labels,S.source.zeroPin.exact,S.source.zeroPin.ordinary⟩
  have hp : P.network.denote=fun x=>NRJordanPowers.pin S.source.scalar (x 0) := by
    funext x
    have hx : (fun _ : Fin 1=>x 0)=x := by
      funext i
      exact congrArg x (Fin.eq_zero i).symm
    rw [←hx]
    cases h : x 0
    · simpa only [h,NRJordanPowers.pin,Bool.false_eq_true,ite_false] using S.source.zeroPinFalse
    · simpa only [h,NRJordanPowers.pin,ite_true] using S.source.zeroPinTrue
  exact ⟨JordanUnaryAccess.extension S.source.F S.source.H J Subtype.val_injective P
    S.source.scalar S.source.scalarNonzero hp v hv⟩

theorem unary_family_extension (V : List (Bool→S.source.K)) (hv : ∀v∈V,v≠0) :
    letI : Algebra ℚ S.source.K := S.source.K.algebra'
    Nonempty (JordanUnaryAccess.FamilyExtension S.source.F S.source.H V) := by
  letI : Algebra ℚ S.source.K := S.source.K.algebra'
  obtain ⟨J⟩ := S.jordan_receipt
  let P : Macro S.source.H 1 :=
    ⟨S.source.zeroPin.network,S.source.zeroPin.labels,S.source.zeroPin.exact,S.source.zeroPin.ordinary⟩
  have hp : P.network.denote=fun x=>NRJordanPowers.pin S.source.scalar (x 0) := by
    funext x
    have hx : (fun _ : Fin 1=>x 0)=x := by
      funext i
      exact congrArg x (Fin.eq_zero i).symm
    rw [←hx]
    cases h : x 0
    · simpa only [h,NRJordanPowers.pin,Bool.false_eq_true,ite_false] using S.source.zeroPinFalse
    · simpa only [h,NRJordanPowers.pin,ite_true] using S.source.zeroPinTrue
  exact ⟨JordanUnaryAccess.familyExtension S.source.F S.source.H J Subtype.val_injective P
    S.source.scalar S.source.scalarNonzero hp V hv⟩

end
end Paper2.Paper1Proved.OddUnary.IsotropicWSource

