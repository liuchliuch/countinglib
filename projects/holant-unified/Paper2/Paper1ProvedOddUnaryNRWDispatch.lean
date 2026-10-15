import Paper2.Paper1ProvedOddUnaryNRUnaryExit
import Paper2.Paper1ProvedOddUnaryNRBinaryActual
import Paper2.Paper1ProvedOddUnaryNRMinarity

/-! Concrete whole-family W dispatch. Every high-arity graph descends by
actual dual caps; the unary branch supplies a genuine Jordan graph and the
binary branch reconstructs NR. The remaining ternary has closed literal
binary slices, over the original retained table and field. -/
namespace Paper2.Paper1Proved.OddUnary.NRCanonical
open Paper2.ExactInput
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {K : IntermediateField ℚ AlgebraicComplex} {r : ℕ} {a : ℕ → ℕ}
variable {H : (i : Fin r) → Holant.Signature K (a i.val)}
variable {R : InvertibleKernel} {v : Bool → AlgebraicComplex}

structure TernaryExit (C : Receipt (H:=H) K.subtype R v) : Type where
  graph : NoXOrdinaryGraphAdjoin.Output H 3
  outside : ¬NR.Closed
    (C.basis.symm.action (RingHomRealization.mapSignature K.subtype graph.network.denote))
  slices : ∀ i b,NR.Closed (NR.slice
    (C.basis.symm.action (RingHomRealization.mapSignature K.subtype graph.network.denote)) i b)

/-- Whole-family negativity constructs the minimum itself. No outside-NR
source or successful-descent assumption is supplied by the caller. -/
theorem canonical_exits (C : Receipt (H:=H) K.subtype R v)
    (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H)) :
    Nonempty (JordanReceipt (H:=H) K.subtype) ∨ Nonempty (TernaryExit C) := by
  obtain ⟨M⟩ := NR.whole_family_coordinate_minimum K H C.basis C.isotropic negative
  have bound := M.arity_le_three C.caps C.capScalars C.capNonzero C.dual
  rcases M with ⟨m,positive,N,outside,least⟩
  change m≤3 at bound
  have lower : ∀ k,k<m → ∀ U : NoXOrdinaryGraphAdjoin.Output H k,
      NR.Closed (C.basis.symm.action (RingHomRealization.mapSignature K.subtype U.network.denote)) := by
    intro k bound U
    by_contra outside
    have smaller := least k U outside
    omega
  have cases : m=1 ∨ m=2 ∨ m=3 := by omega
  rcases cases with rfl|rfl|rfl
  · exact Or.inl (NRUnaryExit.jordan_receipt C N outside)
  · exact False.elim (outside (NR.closed_binary_of_actual_caps
      (K:=K) (r:=r) (a:=a) (H:=H) K.subtype C.basis
      C.caps C.capScalars C.capNonzero C.dual (lower 1 (by omega)) N))
  · refine Or.inr ⟨{ graph := N, outside := outside, slices := ?_ }⟩
    intro i b
    have closed := lower 2 (by omega) (NR.ActualCaps.output
      (K:=K) (r:=r) (a:=a) (H:=H) (n:=2) (C.caps b) N i)
    rw [NR.ActualCaps.chart_denote (K:=K) (r:=r) (a:=a) (H:=H) (n:=2)
      K.subtype C.basis (C.caps b) b
      (C.capScalars b) (C.dual b) N i] at closed
    exact (NR.closed_scale_iff (C.capScalars b) (C.capNonzero b) _).mp closed

/-- The source's actual W graph and original unary produce either a true
Jordan receipt or a concrete least ternary obstruction in its proved NR
chart. All labels, coefficients and source reductions remain retained. -/
theorem source_exits {L : Language} (S : IsotropicWSource L) :
    Nonempty (JordanReceipt (H:=S.source.H) S.source.K.subtype) ∨
      ∃ R : InvertibleKernel,∃ v : Bool → AlgebraicComplex,
        ∃ C : Receipt (H:=S.source.H) S.source.K.subtype R v,
          Nonempty (TernaryExit C) := by
  rcases concrete_exits S with jordan|⟨R,v,⟨C⟩⟩
  · exact Or.inl jordan
  · rcases canonical_exits C S.source.negative with jordan|ternary
    · exact Or.inl jordan
    · exact Or.inr ⟨R,v,C,ternary⟩

end
end Paper2.Paper1Proved.OddUnary.NRCanonical

