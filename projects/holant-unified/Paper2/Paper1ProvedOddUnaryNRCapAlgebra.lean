import Paper2.Paper1ProvedOddUnaryNRComplete
import Holant.Tractable.Criteria

/-! Exact cap/slice identities in an arbitrary common coordinate chart. A
physical cap selects a coordinate only when its actual pairings with the
chart columns have the required nonzero literal selector form. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {K : Type*} [Field K]

def cap {n : ℕ} (u : Holant.Signature K 1) (f : Holant.Signature K (n+1))
    (i : Fin (n+1)) : Holant.Signature K n :=
  fun x => ∑ v : Bool,u (fun _ => v)*f (i.insertNth v x)

def columnPair (u : Holant.Signature K 1) (R : Holant.Kernel K) (b : Bool) : K :=
  ∑ v : Bool,u (fun _ => v)*R v b

theorem action_insert {n : ℕ} (R : Holant.Kernel K)
    (g : Holant.Signature K (n+1)) (i : Fin (n+1)) (v : Bool) (x : Fin n → Bool) :
    Holant.Signature.coordinateAction (fun _ => R) g (i.insertNth v x)=
      ∑ b : Bool,∑ y : Fin n → Bool,
        (R v b*(∏ j,R (x j) (y j)))*g (i.insertNth b y) := by
  classical
  let E := Fin.insertNthEquiv (fun _ : Fin (n+1) => Bool) i
  unfold Holant.Signature.coordinateAction
  rw [←E.sum_comp]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro y _
  change ((∏ j,R ((i.insertNth v x : Fin (n+1) → Bool) j)
    ((i.insertNth b y : Fin (n+1) → Bool) j))*g (i.insertNth b y))=_
  rw [Fin.prod_univ_succAbove _ i]
  simp

theorem cap_action {n : ℕ} (R : Holant.Kernel K) (u : Holant.Signature K 1)
    (g : Holant.Signature K (n+1)) (i : Fin (n+1)) :
    cap u (Holant.Signature.coordinateAction (fun _ => R) g) i=
      Holant.Signature.coordinateAction (fun _ => R)
        (fun x => ∑ b : Bool,columnPair u R b*g (i.insertNth b x)) := by
  classical
  funext x
  unfold cap
  simp only [action_insert]
  unfold Holant.Signature.coordinateAction
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ b : Bool,∑ v : Bool,∑ y : Fin n → Bool,
      u (fun _ => v)*((R v b*(∏ j,R (x j) (y j)))*g (i.insertNth b y)))=
      ∑ b : Bool,∑ y : Fin n → Bool,∑ v : Bool,
        u (fun _ => v)*((R v b*(∏ j,R (x j) (y j)))*g (i.insertNth b y)) := by
          apply Finset.sum_congr rfl
          intro b _
          rw [Finset.sum_comm]
    _ =∑ b : Bool,∑ y : Fin n → Bool,
      columnPair u R b*((∏ j,R (x j) (y j))*g (i.insertNth b y)) := by
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro y _
        unfold columnPair
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro v _
        ring
    _ =∑ y : Fin n → Bool,∑ b : Bool,
      (∏ j,R (x j) (y j))*(columnPair u R b*g (i.insertNth b y)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro b _
        ring

theorem cap_action_of_dual {n : ℕ} (R : Holant.Kernel K) (u : Holant.Signature K 1)
    (b : Bool) (a : K) (dual : ∀ v,columnPair u R v=if v=b then a else 0)
    (g : Holant.Signature K (n+1)) (i : Fin (n+1)) :
    cap u (Holant.Signature.coordinateAction (fun _ => R) g) i=
      Holant.Signature.coordinateAction (fun _ => R) (fun x => a*slice g i b x) := by
  rw [cap_action]
  congr 1
  funext x
  simp only [dual,Fintype.sum_bool,slice]
  cases b <;> simp

theorem cap_chart {n : ℕ} (R : Holant.Tractable.InvertibleKernel)
    (u : Holant.Signature AlgebraicComplex 1) (b : Bool) (a : AlgebraicComplex)
    (dual : ∀ v,columnPair u R.matrix v=if v=b then a else 0)
    (f : Holant.Signature AlgebraicComplex (n+1)) (i : Fin (n+1)) :
    R.symm.action (cap u f i)=fun x => a*slice (R.symm.action f) i b x := by
  have form : cap u f i=R.action (fun x => a*slice (R.symm.action f) i b x) := by
    have h := cap_action_of_dual R.matrix u b a dual (R.symm.action f) i
    change cap u (R.action (R.symm.action f)) i=R.action _ at h
    simpa only [InvertibleKernel.action_symm_action] using h
  rw [form,InvertibleKernel.symm_action_action]

end
end Paper2.Paper1Proved.OddUnary.NR

