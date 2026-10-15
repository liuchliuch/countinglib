import Counting.Algorithm.Holographic.Network
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! Concrete clients check asymmetric matrices, ordered endpoints, open boundary
covariance, and a genuinely three-element domain. All value proofs are kernel
proofs from finite sums, with no native evaluator axiom. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Counting.Algorithm.Holographic.Clients

open scoped BigOperators
open Model

/-- A single vertex whose ordered ports are the boundary, with no internal edges. -/
def corollaShape (n : Nat) : KernelNetworkShape (Fin n) where
  vertices := 1
  arity := fun _ => n
  edges := 0
  ports :=
    { toFun := fun p => .inl p.2
      invFun := fun p => match p with
        | .inl i => ⟨0, i⟩
        | .inr p => Fin.elim0 p.1
      left_inv := by
        rintro ⟨v, i⟩
        have hv : v = 0 := Subsingleton.elim _ _
        subst v
        rfl
      right_inv := by
        intro p
        rcases p with i | ⟨e, b⟩
        · rfl
        · exact Fin.elim0 e }

def corolla {D R : Type} {n : Nat} (f : Signature D R n) : KernelNetwork D R (Fin n) where
  shape := corollaShape n
  vertex := fun _ => f
  edge := Fin.elim0

@[simp] theorem corolla_raw {D R : Type} [Fintype D] [CommSemiring R]
    {n : Nat} (f : Signature D R n) (x : Fin n → D) :
    (corolla f).raw x = f x := by
  simp [KernelNetwork.raw, KernelNetwork.weight, corolla, corollaShape]
  rfl

/-- One loop has two distinct, ordered ports at its single vertex. -/
def loopShape : KernelNetworkShape (Fin 0) where
  vertices := 1
  arity := fun _ => 2
  edges := 1
  ports :=
    { toFun := fun p => .inr (0, p.2 == 1)
      invFun := fun p => match p with
        | .inl i => Fin.elim0 i
        | .inr p => ⟨0, if p.2 then 1 else 0⟩
      left_inv := by
        rintro ⟨v, i⟩
        fin_cases v
        fin_cases i <;> rfl
      right_inv := by
        intro p
        rcases p with i | ⟨e, b⟩
        · exact Fin.elim0 i
        · fin_cases e
          cases b <;> rfl }

def loopNetwork {D R : Type} (f E : Kernel D R) : KernelNetwork D R (Fin 0) where
  shape := loopShape
  vertex := fun _ x => f (x (0 : Fin 2)) (x (1 : Fin 2))
  edge := fun _ => E

theorem loop_raw {D R : Type} [Fintype D] [DecidableEq D] [CommSemiring R]
    (f E : Kernel D R) :
    (loopNetwork f E).raw Fin.elim0 = ∑ a : D, ∑ b : D, f a b * E a b := by
  change (∑ z : (Fin 1 × Bool) → D,
    (∏ _v : Fin 1, f (z (0, false)) (z (0, true))) *
      ∏ e : Fin 1, E (z (e, false)) (z (e, true))) = _
  have hzero : (default : Fin 1) = 0 := Subsingleton.elim _ _
  simpa only [Fintype.prod_unique, hzero] using
    sum_halfEdge_products 1 (fun _ a b => f a b * E a b)

/-- A rational shear is invertible but not symmetric or orthogonal. -/
def shear : Kernel Bool ℚ := fun a b => if a then (if b then 1 else 0) else 1

def inverseShear : Kernel Bool ℚ := fun a b => if a then (if b then 1 else 0) else (if b then -1 else 1)

theorem shear_inverse : (shear : Kernel Bool ℚ) * inverseShear = 1 := by
  funext a b
  cases a <;> cases b <;> norm_num [Matrix.mul_apply, shear, inverseShear]

theorem shear_asymmetric : shear false true ≠ shear true false := by decide

/-- The vertex and edge tables are independently asymmetric. -/
def vertexTable : Kernel Bool ℚ := fun a b => if a then (if b then 7 else 5) else (if b then 3 else 2)
def edgeTable : Kernel Bool ℚ := fun a b => if a then (if b then 19 else 17) else (if b then 13 else 11)

theorem loop_value :
    (loopNetwork vertexTable edgeTable).toOpenInstance.partition Fin.elim0 = 279 := by
  rw [KernelNetwork.partition_toOpenInstance, loop_raw]
  norm_num [vertexTable, edgeTable]

/-- Both transformed tensors contribute; the closed occurrence partition stays 279. -/
theorem transformed_loop_value :
    (transform (loopNetwork vertexTable edgeTable) shear inverseShear).toOpenInstance.partition
      Fin.elim0 = 279 := by
  rw [partition_transform_closed _ _ _ shear_inverse]
  exact loop_value

/-- The first and second endpoints cannot be exchanged for an asymmetric edge. -/
theorem reversed_edge_value :
    (loopNetwork vertexTable edgeTable.transpose).toOpenInstance.partition Fin.elim0 = 271 := by
  rw [KernelNetwork.partition_toOpenInstance, loop_raw]
  norm_num [vertexTable, edgeTable, Matrix.transpose_apply]

/-- The literal forward pullback is not the original equality edge for this basis. -/
theorem transformed_equality_edge : pullback (1 : Kernel Bool ℚ) shear true true = 2 := by
  norm_num [pullback, Matrix.mul_apply, shear]

private theorem binary_action (N f : Kernel Bool ℚ) (x : Fin 2 → Bool) :
    coordinateAction (fun _ => N) (fun y : Fin 2 → Bool => f (y 0) (y 1)) x =
      ∑ a : Bool, ∑ b : Bool, N (x 0) a * N (x 1) b * f a b := by
  unfold coordinateAction
  rw [← (finTwoArrowEquiv Bool).symm.sum_comp, Fintype.sum_prod_type]
  change (∑ a : Bool, ∑ b : Bool,
    (∏ j : Fin 2, N (x j) (![a, b] j)) * f a b) = _
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem open_original_value :
    (corolla (fun x : Fin 2 → Bool => vertexTable (x 0) (x 1))).toOpenInstance.partition
      ![false, true] = 3 := by
  rw [KernelNetwork.partition_toOpenInstance, corolla_raw]
  norm_num [vertexTable]

/-- A free boundary keeps the inverse action: this entry becomes -4, not 3. -/
theorem open_transformed_value :
    (transform (corolla (fun x : Fin 2 → Bool => vertexTable (x 0) (x 1)))
      shear inverseShear).toOpenInstance.partition ![false, true] = -4 := by
  rw [KernelNetwork.partition_toOpenInstance, raw_transform _ _ _ shear_inverse]
  have hc : (corolla (fun x : Fin 2 → Bool => vertexTable (x 0) (x 1))).raw =
      fun x => vertexTable (x 0) (x 1) := funext (corolla_raw _)
  rw [hc, binary_action]
  norm_num [inverseShear, vertexTable]

theorem open_not_invariant :
    (transform (corolla (fun x : Fin 2 → Bool => vertexTable (x 0) (x 1)))
      shear inverseShear).toOpenInstance.partition ≠
      (corolla (fun x : Fin 2 → Bool => vertexTable (x 0) (x 1))).toOpenInstance.partition := by
  intro h
  have he := congrFun h ![false, true]
  rw [open_transformed_value, open_original_value] at he
  norm_num at he

/-- Reversing the ordered boundary tuple changes the transformed entry. -/
theorem open_reversed_value :
    (transform (corolla (fun x : Fin 2 → Bool => vertexTable (x 0) (x 1)))
      shear inverseShear).toOpenInstance.partition ![true, false] = -2 := by
  rw [KernelNetwork.partition_toOpenInstance, raw_transform _ _ _ shear_inverse]
  have hc : (corolla (fun x : Fin 2 → Bool => vertexTable (x 0) (x 1))).raw =
      fun x => vertexTable (x 0) (x 1) := funext (corolla_raw _)
  rw [hc, binary_action]
  norm_num [inverseShear, vertexTable]

/-- A three-state permutation basis demonstrates the general finite-domain API. -/
def cycle3 : Kernel (Fin 3) ℚ := fun a b => if b = a + 1 then 1 else 0

def inverseCycle3 : Kernel (Fin 3) ℚ := cycle3.transpose

theorem cycle3_inverse : cycle3 * inverseCycle3 = 1 := by
  funext a b
  fin_cases a <;> fin_cases b <;>
    norm_num [cycle3, inverseCycle3, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transpose_apply]

def ternaryVertex : Kernel (Fin 3) ℚ := fun a b => (a.val + 1 : Nat) * (b.val + 2 : Nat)

theorem ternary_loop_value :
    (loopNetwork ternaryVertex (1 : Kernel (Fin 3) ℚ)).toOpenInstance.partition Fin.elim0 = 20 := by
  rw [KernelNetwork.partition_toOpenInstance, loop_raw]
  norm_num [ternaryVertex, Fin.sum_univ_succ, Matrix.one_apply]

theorem ternary_transformed_loop_value :
    (transform (loopNetwork ternaryVertex (1 : Kernel (Fin 3) ℚ)) cycle3 inverseCycle3).toOpenInstance.partition Fin.elim0 = 20 := by
  rw [partition_transform_closed _ _ _ cycle3_inverse]
  exact ternary_loop_value

end Counting.Algorithm.Holographic.Clients
