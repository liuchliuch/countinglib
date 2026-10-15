import Paper2.Paper1ProvedOddUnaryNRCanonicalSource

/-! The sourced isotropic W case has a concrete ordinary graph and pin.
It either has the genuine nonzero Jordan coefficient, retained explicitly,
or supplies the exceptional NR chart with two actual dual caps. -/
namespace Paper2.Paper1Proved.OddUnary.NRCanonical
open Paper2.ExactInput
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

structure Prepared {L : Language} (S : IsotropicWSource L) : Type 1 where
  ternary : Macro S.source.H 3
  pin : Macro S.source.H 1
  frame : InvertibleKernel
  vector : Bool → AlgebraicComplex
  delta : AlgebraicComplex
  deltaNonzero : delta≠0
  isotropic : frame.matrix false false^2+frame.matrix true false^2=0
  normNonzero : vector false^2+vector true^2≠0
  alphaNonzero : alpha frame.matrix vector≠0
  ternaryForm : RingHomRealization.mapSignature S.source.K.subtype ternary.network.denote=
    fun x => delta*GlobalCloseCompletionIndependentPinsWCore.image frame.matrix x
  pinForm : RingHomRealization.mapSignature S.source.K.subtype pin.network.denote=
    fun x => vector (x 0)

theorem prepare {L : Language} (S : IsotropicWSource L) : Nonempty (Prepared S) := by
  obtain ⟨N,R,delta,hd,r0,-,iso,form⟩ := S.symmetric_graph
  let P : Macro S.source.H 1 :=
    ⟨S.source.zeroPin.network,S.source.zeroPin.labels,S.source.zeroPin.exact,S.source.zeroPin.ordinary⟩
  let c := S.source.K.subtype S.source.scalar
  have hc : c≠0 := S.source.K.subtype.injective.ne S.source.scalarNonzero
  let v : Bool → AlgebraicComplex := fun b => if b then 0 else c
  have pin : RingHomRealization.mapSignature S.source.K.subtype P.network.denote=fun x => v (x 0) := by
    funext x
    have hx : (fun _ : Fin 1 => x 0)=x := by
      funext i
      exact congrArg x (Fin.eq_zero i).symm
    change S.source.K.subtype (P.network.denote x)=_
    rw [←hx]
    cases h : x 0
    · simp only [h,v,Bool.false_eq_true,ite_false]
      change S.source.K.subtype (S.source.zeroPin.network.denote (fun _ => false))=
        S.source.K.subtype S.source.scalar
      exact congrArg S.source.K.subtype S.source.zeroPinFalse
    · simpa [P,v,c,h] using congrArg S.source.K.subtype S.source.zeroPinTrue
  have norm : v false^2+v true^2≠0 := by
    simpa only [v,Bool.false_eq_true,ite_false,ite_true,zero_pow (by decide : 2≠0),add_zero] using pow_ne_zero 2 hc
  have ha : alpha R.matrix v≠0 := by
    simpa [alpha,v] using mul_ne_zero r0 hc
  exact ⟨{
    ternary := N
    pin := P
    frame := R
    vector := v
    delta := delta
    deltaNonzero := hd
    isotropic := iso
    normNonzero := norm
    alphaNonzero := ha
    ternaryForm := form
    pinForm := pin }⟩

theorem Prepared.receipt_or_jordan {L : Language} {S : IsotropicWSource L} (I : Prepared S) :
    ¬exceptional I.frame.matrix I.vector ∨
      Nonempty (Receipt (H:=S.source.H) S.source.K.subtype I.frame I.vector) := by
  by_cases h : exceptional I.frame.matrix I.vector
  · exact Or.inr (receipt S.source.K.subtype I.ternary I.pin I.frame I.vector I.delta
      I.deltaNonzero I.isotropic I.normNonzero I.alphaNonzero h I.ternaryForm I.pinForm)
  · exact Or.inl h

theorem canonical_or_jordan {L : Language} (S : IsotropicWSource L) :
    ∃ I : Prepared S,¬exceptional I.frame.matrix I.vector ∨
      Nonempty (Receipt (H:=S.source.H) S.source.K.subtype I.frame I.vector) := by
  obtain ⟨I⟩ := prepare S
  exact ⟨I,I.receipt_or_jordan⟩

end
end Paper2.Paper1Proved.OddUnary.NRCanonical

