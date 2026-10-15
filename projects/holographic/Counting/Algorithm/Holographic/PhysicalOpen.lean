import Counting.Algorithm.Holographic.Upstream
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpen

/-!
# The actual physical source graph as an S1 open instance

This optional bridge retains the original palette, literal transformed labels,
native-edge condition, fixed algebraic field, and supplied invertible basis.
It applies the frozen `fromHolographicOpen` construction and relates its actual
source graph (after coefficient embedding) to the common S1 partition. It adds
no pinning/equality resources and asserts no variable-basis search bound.
-/

noncomputable section

namespace Counting.Algorithm.Holographic.PhysicalOpen

open Holant Holant.Algebraic Holant.Tractable Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosurePhysicalBridge

variable {s : Nat} {a : Nat → Nat}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (P : Palette G) (B : InvertibleKernel) {n : Nat} (N : Network AlgebraicComplex n)
variable (labels : ∀ v, (⟨N.shape.arity v, N.vertex v⟩ : AnySignature AlgebraicComplex) ∈
  familyAction B (RH.mapFamily (algebraicEmbedding G) P.family))
variable (edges : ∀ e, N.edge e = Holant.Kernel.pullback Signature.disequality B.inverse)

/-- Covariance of the actual constructed source graph, expanded as S1 occurrences.
Every hypothesis is the original physical construction's resource contract. -/
theorem source_partition_covariance :
    let d := fromHolographicOpen G P B N labels edges
    (Bridge.Holant.adapt (d.access.source.map (algebraicEmbedding G))).toOpenInstance.partition =
      coordinateAction (fun _ => B.inverse) (Bridge.Holant.adapt N).toOpenInstance.partition := by
  dsimp only
  let d := fromHolographicOpen G P B N labels edges
  change (Bridge.Holant.adapt (d.access.source.map (algebraicEmbedding G))).toOpenInstance.partition = _
  have hp (H : Model.KernelNetwork Bool AlgebraicComplex (Fin n)) :
      H.toOpenInstance.partition = H.raw :=
    funext (Model.KernelNetwork.partition_toOpenInstance H)
  rw [hp, hp, Bridge.Holant.raw_adapt, Bridge.Holant.raw_adapt,
    d.access.mappedNetwork, d.restoredIdentity]
  exact restoredOpen_denote B N

/-- The original ordered boundary is recovered by the supplied forward matrix;
the S1 result concerns the same physically constructed source graph. -/
theorem source_partition_recovery :
    let d := fromHolographicOpen G P B N labels edges
    coordinateAction (fun _ => B.matrix)
      (Bridge.Holant.adapt (d.access.source.map (algebraicEmbedding G))).toOpenInstance.partition =
        (Bridge.Holant.adapt N).toOpenInstance.partition := by
  dsimp only
  rw [source_partition_covariance G P B N labels edges]
  exact coordinateAction_cancel (fun _ => B.matrix) (fun _ => B.inverse)
    (fun _ => B.matrix_inverse) _

/-- The source keeps the original incidence geometry before occurrence expansion. -/
theorem source_same_shape :
    let d := fromHolographicOpen G P B N labels edges
    (Bridge.Holant.adapt d.access.source).shape = (Bridge.Holant.adapt N).shape := by
  dsimp only
  exact congrArg Bridge.Holant.adaptShape
    ((fromHolographicOpen G P B N labels edges).access.sameShape.trans
      (fromHolographicOpen G P B N labels edges).sameShape)

end Counting.Algorithm.Holographic.PhysicalOpen
