import Counting.Algorithm.Holographic.Network
import Counting.Bridge.Holant
import Holant.Proofs.Closure.ClosurePhysicalBridgeHolographicOpenAlgebra

/-!
# Compatibility with the unique frozen Boolean provider

The source imports `Holant.Holographic`; the Boolean theorems below use its
closed proof and the frozen open extension, after identifying the actual
transformed S1 network. No original `Holant` provider is copied or renamed.
-/

namespace Counting.Algorithm.Holographic.Upstream

open scoped BigOperators

variable {R : Type} [CommSemiring R] {n : Nat}

@[simp] theorem mul_eq (M N : Kernel Bool R) : M * N = Holant.Kernel.mul M N := rfl

@[simp] theorem one_eq : (1 : Kernel Bool R) = Holant.Signature.equality := rfl

@[simp] theorem pullback_eq (E M : Kernel Bool R) :
    pullback E M = Holant.Kernel.pullback E M := rfl

@[simp] theorem action_eq (A : Fin n → Kernel Bool R) (f : Model.Signature Bool R n) :
    coordinateAction A f = Holant.Signature.coordinateAction A f := rfl

/-- The transformed S1 network is the adaptation of the original transformation,
with literal equality of shape, ordered vertex tables, and edge kernels. -/
theorem adapt_transform (G : Holant.Network R n) (M N : Kernel Bool R) :
    transform (Bridge.Holant.adapt G) M N =
      Bridge.Holant.adapt
        (Holant.LocalDrafts.RemoteWork.StableClosureV2.OpenHolographic.transform G M N) := rfl

/-- Direct reuse of the frozen closed-network theorem, reaching the common
occurrence partition through S1's existing adapter. -/
theorem closed_partition (G : Holant.Network R 0) (M N : Kernel Bool R)
    (hMN : M * N = 1) :
    (transform (Bridge.Holant.adapt G) M N).toOpenInstance.partition =
      (Bridge.Holant.adapt G).toOpenInstance.partition := by
  funext x
  rw [Model.KernelNetwork.partition_toOpenInstance,
    Model.KernelNetwork.partition_toOpenInstance, adapt_transform,
    Bridge.Holant.raw_adapt, Bridge.Holant.raw_adapt]
  exact congrFun (Holant.Network.denote_holographicTransform G M N hMN) x

/-- Direct reuse of the frozen open theorem. The right side retains the action
on every ordered boundary coordinate of the actual occurrence partition. -/
theorem open_partition (G : Holant.Network R n) (M N : Kernel Bool R)
    (hMN : M * N = 1) :
    (transform (Bridge.Holant.adapt G) M N).toOpenInstance.partition =
      coordinateAction (fun _ => N) (Bridge.Holant.adapt G).toOpenInstance.partition := by
  have hp (H : Model.KernelNetwork Bool R (Fin n)) : H.toOpenInstance.partition = H.raw :=
    funext (Model.KernelNetwork.partition_toOpenInstance H)
  rw [hp, hp, adapt_transform, Bridge.Holant.raw_adapt, Bridge.Holant.raw_adapt, action_eq]
  exact Holant.LocalDrafts.RemoteWork.StableClosureV2.OpenHolographic.denote_transform G M N hMN

end Counting.Algorithm.Holographic.Upstream
