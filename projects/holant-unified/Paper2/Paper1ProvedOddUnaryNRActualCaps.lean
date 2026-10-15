import Paper2.Paper1ProvedOddUnaryNRCapAlgebra
import Paper2.Paper1ProvedOddUnaryNRTransport
import Paper2.Paper1ProvedOddUnaryCapBasis
import Mathlib.Logic.Equiv.Fin.Basic

/-! Physical coordinate slices for the sheared-class descent. Every cap is an
actual graph in the original ordinary table; reordering only changes boundary
names. The coordinate identity follows from the proved column pairings. -/
namespace Paper2.Paper1Proved.OddUnary.NR.ActualCaps
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddNonisotropicFrame
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def order {n : ℕ} (i : Fin (n+1)) : Equiv.Perm (Fin (n+1)) :=
  (finSuccEquiv' i).trans (finSuccEquiv' (0 : Fin (n+1))).symm

theorem order_word {n : ℕ} (i : Fin (n+1)) (v : Bool) (x : Fin n → Bool) :
    (fun j => (Fin.cons v x : Fin (n+1) → Bool) (order i j))=(i.insertNth v x : Fin (n+1) → Bool) := by
  funext j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp [order]
  · simp [order,Fin.zero_succAbove]

variable {K : Type} [Field K] {r n : ℕ} {a : ℕ → ℕ}
variable {H : (j : Fin r) → Holant.Signature K (a j.val)}

def graph (P : NoXOrdinaryGraphAdjoin.Output H 1)
    (N : NoXOrdinaryGraphAdjoin.Output H (n+1)) (i : Fin (n+1)) : Holant.Network K n :=
  capHead P.network (reboundary N.network (order i))

theorem graph_uses (P : NoXOrdinaryGraphAdjoin.Output H 1)
    (N : NoXOrdinaryGraphAdjoin.Output H (n+1)) (i : Fin (n+1)) :
    Uses (graph P N i) (Set.range (fun j : Fin r =>
      (⟨a j.val,H j⟩ : Holant.AnySignature K))) := by
  apply capHead_uses
  · intro v
    exact ⟨P.labels.vertex v,P.exact v⟩
  · intro v
    exact ⟨N.labels.vertex v,N.exact v⟩

def labels (P : NoXOrdinaryGraphAdjoin.Output H 1)
    (N : NoXOrdinaryGraphAdjoin.Output H (n+1)) (i : Fin (n+1)) :
    Labelling (graph P N i).shape r 1 a where
  vertex v := Classical.choose (graph_uses P N i v)
  vertex_arity v := congrArg Sigma.fst (Classical.choose_spec (graph_uses P N i v))
  edge _ := 0

theorem exact (P : NoXOrdinaryGraphAdjoin.Output H 1)
    (N : NoXOrdinaryGraphAdjoin.Output H (n+1)) (i : Fin (n+1)) :
    LabelledNetwork.Exact H (graph P N i) (labels P N i) := by
  intro v
  exact Classical.choose_spec (graph_uses P N i v)

def output (P : NoXOrdinaryGraphAdjoin.Output H 1)
    (N : NoXOrdinaryGraphAdjoin.Output H (n+1)) (i : Fin (n+1)) :
    NoXOrdinaryGraphAdjoin.Output H n :=
  ⟨graph P N i,labels P N i,exact P N i,
    capHead_ordinary P.network _ P.ordinary N.ordinary⟩

theorem denote (P : NoXOrdinaryGraphAdjoin.Output H 1)
    (N : NoXOrdinaryGraphAdjoin.Output H (n+1)) (i : Fin (n+1)) :
    (output P N i).network.denote=NR.cap P.network.denote N.network.denote i := by
  funext x
  change (capHead P.network (reboundary N.network (order i))).denote x=_
  rw [capHead_denote]
  simp only [reboundary_denote]
  simp only [NR.cap,Fintype.sum_bool]
  rw [order_word,order_word]
  exact add_comm _ _

theorem mapped_denote (phi : K →+* AlgebraicComplex)
    (P : NoXOrdinaryGraphAdjoin.Output H 1)
    (N : NoXOrdinaryGraphAdjoin.Output H (n+1)) (i : Fin (n+1)) :
    RingHomRealization.mapSignature phi (output P N i).network.denote=
      NR.cap (RingHomRealization.mapSignature phi P.network.denote)
        (RingHomRealization.mapSignature phi N.network.denote) i := by
  funext x
  change phi ((output P N i).network.denote x)=_
  rw [denote]
  simp [NR.cap,map_mul,RingHomRealization.mapSignature]

theorem chart_denote (phi : K →+* AlgebraicComplex)
    (R : Holant.Tractable.InvertibleKernel)
    (P : NoXOrdinaryGraphAdjoin.Output H 1)
    (b : Bool) (c : AlgebraicComplex)
    (dual : ∀ v,NR.columnPair (RingHomRealization.mapSignature phi P.network.denote)
      R.matrix v=if v=b then c else 0)
    (N : NoXOrdinaryGraphAdjoin.Output H (n+1)) (i : Fin (n+1)) :
    R.symm.action (RingHomRealization.mapSignature phi (output P N i).network.denote)=
      fun x => c*NR.slice
        (R.symm.action (RingHomRealization.mapSignature phi N.network.denote)) i b x := by
  rw [mapped_denote]
  exact NR.cap_chart R _ b c dual _ i

/-- The high-arity failure has an actual ordinary one-cap descendant that
still fails the same exact tensor criterion. -/
theorem exists_outside_cap (phi : K →+* AlgebraicComplex)
    (R : Holant.Tractable.InvertibleKernel)
    (caps : Bool → NoXOrdinaryGraphAdjoin.Output H 1)
    (c : Bool → AlgebraicComplex) (cnz : ∀ b,c b≠0)
    (dual : ∀ b v,NR.columnPair (RingHomRealization.mapSignature phi (caps b).network.denote)
      R.matrix v=if v=b then c b else 0)
    (N : NoXOrdinaryGraphAdjoin.Output H (n+1)) (large : 4≤n+1)
    (outside : ¬NR.Closed
      (R.symm.action (RingHomRealization.mapSignature phi N.network.denote))) :
    ∃ i b,¬NR.Closed
      (R.symm.action (RingHomRealization.mapSignature phi (output (caps b) N i).network.denote)) := by
  obtain ⟨i,b,failure⟩ := NR.exists_not_closed_slice_of_four_le _ large outside
  refine ⟨i,b,?_⟩
  rw [chart_denote phi R (caps b) b (c b) (dual b) N i]
  exact fun h => failure ((NR.closed_scale_iff (c b) (cnz b) _).mp h)

end
end Paper2.Paper1Proved.OddUnary.NR.ActualCaps

