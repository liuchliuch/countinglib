import Paper2.Paper1ProvedOddUnaryJordanTraceZeroGraph
import Paper2.Paper1ProvedOddUnaryJordanScaledGraphAdjoin
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZTrace

/-! Install the actual trace-zero graph and both literal unit pins in one
finite table over the unchanged original field. The back programme is the
composition of the checked graph and Jordan unary programmes. -/
namespace Paper2.Paper1Proved.OddUnary.JordanTraceZeroPins
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedGadgetSubstitution Holant.Complexity.BinaryCompose
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2 OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace T
export GlobalCloseCompletionSymmetricGHZTrace (binary)
end T
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {degree r : ℕ} {a : ℕ→ℕ}
variable (F : FixedField K degree) (H : (i : Fin r)→Holant.Signature K (a i.val))

structure Packet where
  count : ℕ
  arity : ℕ→ℕ
  signatures : (i : Fin count)→Holant.Signature K (arity i.val)
  old : Fin r→Fin count
  old_literal : ∀i,(⟨arity (old i).val,signatures (old i)⟩ : Holant.AnySignature K)=⟨a i.val,H i⟩
  p : Bool→Fin count
  hp : ∀b,(⟨arity (p b).val,signatures (p b)⟩ : Holant.AnySignature K)=
    ⟨1,QuaternaryUnaryAccess.pin b⟩
  diagonal : K
  offDiagonal : K
  traceLabel : Fin count
  trace_literal : (⟨arity traceLabel.val,signatures traceLabel⟩ : Holant.AnySignature K)=
    ⟨2,T.binary diagonal offDiagonal offDiagonal⟩
  nonsingular : -diagonal^2-offDiagonal^2≠0
  back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding count 1 arity) F.encoding
    (RawClosedNetwork.validatedEncoding r 1 a) F.encoding
    ((QuaternaryOrdinaryCompanion.tables F signatures).evaluate F)
    ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)

omit [CharZero K] in
theorem trace_form (E : JordanTraceZeroGraph.Extension (H:=H) F) :
    E.graph.network.denote=T.binary (JordanTraceZeroGraph.matrix E.graph false false)
      (JordanTraceZeroGraph.matrix E.graph false true)
      (JordanTraceZeroGraph.matrix E.graph false true) := by
  have last : JordanTraceZeroGraph.matrix E.graph true true=
      -JordanTraceZeroGraph.matrix E.graph false false := by
    have ht := E.tracezero
    change JordanTraceZeroGraph.matrix E.graph false false+
      JordanTraceZeroGraph.matrix E.graph true true=0 at ht
    linear_combination ht
  have hs := E.symmetric true false
  funext x
  have hw : x=![x 0,x 1] := by funext i;fin_cases i <;> rfl
  rw [hw]
  cases x 0 <;> cases x 1 <;>
    simp only [T.binary,Matrix.cons_val_zero,Matrix.cons_val_one,
      Bool.false_eq_true,ite_true,ite_false]
  · rfl
  · rfl
  · exact hs
  · exact last

omit [CharZero K] in
theorem trace_nonsingular (E : JordanTraceZeroGraph.Extension (H:=H) F) :
    -(JordanTraceZeroGraph.matrix E.graph false false)^2-
      (JordanTraceZeroGraph.matrix E.graph false true)^2≠0 := by
  have last : JordanTraceZeroGraph.matrix E.graph true true=
      -JordanTraceZeroGraph.matrix E.graph false false := by
    have ht := E.tracezero
    change JordanTraceZeroGraph.matrix E.graph false false+
      JordanTraceZeroGraph.matrix E.graph true true=0 at ht
    linear_combination ht
  have he : OneHotBinaryProjection.determinant (JordanTraceZeroGraph.matrix E.graph)=
      -(JordanTraceZeroGraph.matrix E.graph false false)^2-
        (JordanTraceZeroGraph.matrix E.graph false true)^2 := by
    unfold OneHotBinaryProjection.determinant
    rw [last,E.symmetric true false]
    ring
  rw [←he]
  exact E.nonsingular

variable {phi : K→+* AlgebraicComplex}

/-- The trace graph is adjoined at scale one, and the two pins are then
installed by the proved original-field Jordan unary interpolation. -/
def install (E : JordanTraceZeroGraph.Extension (H:=H) F)
    (J : NRCanonical.JordanReceipt (H:=H) phi) (injective : Function.Injective phi)
    (P : Macro H 1) (c : K) (hc : c≠0)
    (hP : P.network.denote=fun x=>NRJordanPowers.pin c (x 0)) : Packet F H := by
  classical
  let G := JordanScaledGraphAdjoin.signatures F E.signatures E.graph 1
  let oldG := JordanScaledGraphAdjoin.old E.signatures
  have oldGeq := JordanScaledGraphAdjoin.old_literal F E.signatures E.graph 1
  let J0 := JordanUnaryAccess.retainReceipt H E.signatures E.old E.old_literal J
  let P0 := RetainedTable.liftMacro E.old E.old_literal P
  let J1 := JordanUnaryAccess.retainReceipt E.signatures G oldG oldGeq J0
  let P1 := RetainedTable.liftMacro oldG oldGeq P0
  let V : List (Bool→K) := [fun b=>if b then 0 else 1,fun b=>if b then 1 else 0]
  have hV : ∀v∈V,v≠0 := by
    intro v hv
    rcases List.mem_cons.mp hv with hv|hv
    · subst v
      intro hz
      have h := congrFun hz false
      norm_num at h
    · rcases List.mem_cons.mp hv with hv|hv
      · subst v
        intro hz
        have h := congrFun hz true
        norm_num at h
      · exact (List.not_mem_nil hv).elim
  let U := JordanUnaryAccess.familyExtension F G J1 injective P1 c hc hP V hV
  have hpins (b : Bool) : ∃j:Fin U.count,
      (⟨U.arity j.val,U.signatures j⟩ : Holant.AnySignature K)=
        ⟨1,QuaternaryUnaryAccess.pin b⟩ := by
    cases b
    · obtain ⟨j,hj⟩ := U.unary_literal (fun b=>if b then 0 else 1) (List.mem_cons_self)
      refine ⟨j,hj.trans ?_⟩
      apply congrArg (fun f:Holant.Signature K 1=>(⟨1,f⟩ : Holant.AnySignature K))
      funext x
      cases hx:x 0 <;> simp [QuaternaryUnaryAccess.pin,hx]
    · obtain ⟨j,hj⟩ := U.unary_literal (fun b=>if b then 1 else 0)
        (List.mem_cons_of_mem _ (List.mem_cons_self))
      refine ⟨j,hj.trans ?_⟩
      apply congrArg (fun f:Holant.Signature K 1=>(⟨1,f⟩ : Holant.AnySignature K))
      funext x
      cases hx:x 0 <;> simp [QuaternaryUnaryAccess.pin,hx]
  let p (b : Bool) := Classical.choose (hpins b)
  let new := JordanScaledGraphAdjoin.newLabel E.signatures
  have htrace : (⟨JordanScaledGraphAdjoin.arity E.signatures E.graph new.val,G new⟩ :
      Holant.AnySignature K)=⟨2,T.binary (JordanTraceZeroGraph.matrix E.graph false false)
        (JordanTraceZeroGraph.matrix E.graph false true)
        (JordanTraceZeroGraph.matrix E.graph false true)⟩ := by
    rw [JordanScaledGraphAdjoin.new_literal]
    simp only [div_one]
    rw [trace_form F H E]
  exact {
    count:=U.count
    arity:=U.arity
    signatures:=U.signatures
    old:=fun i=>U.old (oldG (E.old i))
    old_literal:=fun i=>(U.old_literal _).trans ((oldGeq _).trans (E.old_literal i))
    p:=p
    hp:=fun b=>Classical.choose_spec (hpins b)
    diagonal:=JordanTraceZeroGraph.matrix E.graph false false
    offDiagonal:=JordanTraceZeroGraph.matrix E.graph false true
    traceLabel:=U.old new
    trace_literal:=(U.old_literal new).trans htrace
    nonsingular:=trace_nonsingular F H E
    back:=Programme.compose U.back (Programme.compose
      (JordanScaledGraphAdjoin.source F E.signatures E.graph 1 one_ne_zero) E.back) }

end
end Paper2.Paper1Proved.OddUnary.JordanTraceZeroPins
