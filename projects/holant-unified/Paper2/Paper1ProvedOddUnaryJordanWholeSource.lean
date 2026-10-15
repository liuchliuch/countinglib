import Paper2.Paper1ProvedOddUnaryOneHotGeneralProjectionGraph
import Paper2.Paper1ProvedOddUnaryJordanOriginalLine
import Paper2.Paper1ProvedOddUnaryJordanTraceZeroPins

/-! The whole-family obstruction supplies an original-field prime breaking
the actual Jordan line. Executed product-cap interpolation, physical Gram
graphs and Jordan congruence install a nonsingular trace-zero row together
with both literal pins. All controlled reductions return to the original
source table. -/
namespace Paper2.Paper1Proved.OddUnary
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace JordanTraceZeroPins.Packet
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {degree r s : ℕ} {a b : ℕ→ℕ}
variable {F : FixedField K degree}
variable {H : (i : Fin r)→Holant.Signature K (a i.val)}
variable {T : (i : Fin s)→Holant.Signature K (b i.val)}

/-- Compose a checked finite-table extension with an earlier checked
extension, preserving every literal row and the exact output encoding. -/
def precompose (Q : JordanTraceZeroPins.Packet F T)
    (old : Fin r→Fin s)
    (literal : ∀i,(⟨b (old i).val,T (old i)⟩ : Holant.AnySignature K)=⟨a i.val,H i⟩)
    (back : LengthControlledOracleReduction
      (RawClosedNetwork.validatedEncoding s 1 b) F.encoding
      (RawClosedNetwork.validatedEncoding r 1 a) F.encoding
      ((QuaternaryOrdinaryCompanion.tables F T).evaluate F)
      ((QuaternaryOrdinaryCompanion.tables F H).evaluate F)) :
    JordanTraceZeroPins.Packet F H where
  count:=Q.count
  arity:=Q.arity
  signatures:=Q.signatures
  old:=Q.old ∘ old
  old_literal:=fun i=>(Q.old_literal (old i)).trans (literal i)
  p:=Q.p
  hp:=Q.hp
  diagonal:=Q.diagonal
  offDiagonal:=Q.offDiagonal
  traceLabel:=Q.traceLabel
  trace_literal:=Q.trace_literal
  nonsingular:=Q.nonsingular
  back:=Programme.compose Q.back back

end JordanTraceZeroPins.Packet

namespace IsotropicWSource
variable {L : Paper2.ExactInput.Language} (S : IsotropicWSource L)

/-- There is no supplied unary access, binary projection, matching escape,
or trace-zero resource premise. Each is constructed from the actual source
and its whole-family obstruction in the unchanged coefficient field. -/
theorem tracezero_pin_packet :
    letI : Algebra ℚ S.source.K := S.source.K.algebra'
    Nonempty (JordanTraceZeroPins.Packet S.source.F S.source.H) := by
  letI : Algebra ℚ S.source.K := S.source.K.algebra'
  obtain ⟨J⟩:=S.jordan_receipt
  obtain ⟨opposite,c,cnz,line⟩:=J.original_line_orientation
  obtain ⟨n,big,N,prime,outside⟩:=WEscape.residual_outside_prime_graph S opposite
  obtain ⟨m,rfl⟩ : ∃m,n=m+2 := ⟨n-2,by omega⟩
  obtain ⟨V,E,Q,det,live⟩:=S.outside_prime_projection N prime
    (NRJordanPowers.repeated J.ratioK) opposite c cnz line outside
  let J0:=JordanUnaryAccess.retainReceipt S.source.H E.signatures E.old E.old_literal J
  have same_ratio : J0.ratioK=J.ratioK := rfl
  have live0 : OneHotLineProjection.line (NRJordanPowers.repeated J0.ratioK)
      (JordanTraceZeroGraph.matrix Q)≠0 := by
    rw [same_ratio]
    exact live
  obtain ⟨G⟩:=JordanTraceZeroGraph.extension_exists S.source.F J0
    Subtype.val_injective Q det live0
  let P : Macro S.source.H 1:=
    ⟨S.source.zeroPin.network,S.source.zeroPin.labels,
      S.source.zeroPin.exact,S.source.zeroPin.ordinary⟩
  have hp : P.network.denote=fun x=>NRJordanPowers.pin S.source.scalar (x 0) := by
    funext x
    have hx : (fun _ : Fin 1=>x 0)=x := by
      funext i
      exact congrArg x (Fin.eq_zero i).symm
    rw [←hx]
    cases h : x 0
    · simpa only [h,NRJordanPowers.pin,Bool.false_eq_true,ite_false]
        using S.source.zeroPinFalse
    · simpa only [h,NRJordanPowers.pin,ite_true] using S.source.zeroPinTrue
  let P0:=RetainedTable.liftMacro E.old E.old_literal P
  let T:=JordanTraceZeroPins.install S.source.F E.signatures G J0
    Subtype.val_injective P0 S.source.scalar S.source.scalarNonzero hp
  exact ⟨T.precompose E.old E.old_literal E.back⟩

end IsotropicWSource
end
end Paper2.Paper1Proved.OddUnary

