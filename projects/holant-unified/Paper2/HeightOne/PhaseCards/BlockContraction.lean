import Paper2.HeightOne.PhaseCards.WalshTransport
import Paper2.HeightOne.PhaseCards.PhaseRatios

/-! Literal same-block contraction formulas for the source's two-point phase
blocks. Empty residual blocks are retained as their exact scalar, possibly zero. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
attribute [local instance] Classical.propDecidable
open Tractable
open scoped BigOperators
variable {ι : Type} [Fintype ι]

def point (a : ι → Bool) : Tensor AlgebraicComplex ι := fun x => if x = a then 1 else 0

def twoPoint (a : ι → Bool) (r : AlgebraicComplex) : Tensor AlgebraicComplex ι :=
  point a + r • point (fun i => !(a i))

lemma sum_elim_eq_iff {x a : ι → Bool} {v p : Bool → Bool} :
    Sum.elim x v = Sum.elim a p ↔ x = a ∧ v = p := by
  constructor
  · intro h
    exact ⟨funext (fun i => congrFun h (.inl i)), funext (fun b => congrFun h (.inr b))⟩
  · rintro ⟨rfl, rfl⟩; rfl

lemma contractKernel_point (E : Kernel AlgebraicComplex) (a : ι → Bool) (p : Bool → Bool) :
    contractKernel E (point (Sum.elim a p)) = E (p false) (p true) • point a := by
  funext x
  simp only [contractKernel, point, sum_elim_eq_iff, Pi.smul_apply, smul_eq_mul]
  by_cases hx : x = a <;> simp [hx]

lemma contractKernel_add (E : Kernel AlgebraicComplex)
    (f g : Tensor AlgebraicComplex (ι ⊕ Bool)) :
    contractKernel E (f + g) = contractKernel E f + contractKernel E g := by
  funext x
  simp [contractKernel, mul_add, Finset.sum_add_distrib]

lemma contractKernel_scale_tensor (E : Kernel AlgebraicComplex) (r : AlgebraicComplex)
    (f : Tensor AlgebraicComplex (ι ⊕ Bool)) :
    contractKernel E (r • f) = r • contractKernel E f := by
  funext x
  simp only [contractKernel, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

lemma complement_sum_elim (a : ι → Bool) (p : Bool → Bool) :
    (fun i => !(Sum.elim a p i)) = Sum.elim (fun i => !(a i)) (fun b => !(p b)) := by
  funext i
  cases i <;> rfl

/-- Both coefficients are kept. If no ports remain this is the correct scalar
sum; it is never normalized away or silently required to be nonzero. -/
theorem contractKernel_twoPoint (E : Kernel AlgebraicComplex)
    (a : ι → Bool) (p : Bool → Bool) (r : AlgebraicComplex) :
    contractKernel E (twoPoint (Sum.elim a p) r) =
      E (p false) (p true) • point a +
        (r * E (!(p false)) (!(p true))) • point (fun i => !(a i)) := by
  rw [twoPoint, contractKernel_add, contractKernel_scale_tensor, complement_sum_elim,
    contractKernel_point, contractKernel_point, smul_smul]

/-- For the supported orientation, a same-block contraction changes only its
scale and the ratio of its two residual points. -/
theorem contractKernel_twoPoint_ratio (E : Kernel AlgebraicComplex)
    (a : ι → Bool) (p : Bool → Bool) (r κ ρ : AlgebraicComplex)
    (h0 : E (p false) (p true) = κ)
    (h1 : E (!(p false)) (!(p true)) = κ * ρ) :
    contractKernel E (twoPoint (Sum.elim a p) r) = κ • twoPoint a (ρ * r) := by
  rw [contractKernel_twoPoint, h0, h1, twoPoint, smul_add, smul_smul]
  congr 1
  ring

lemma same_block_plus_false (a : ι → Bool) (r s : AlgebraicComplex) :
    contractKernel (plusKernel s) (twoPoint (Sum.elim a (fun _ => false)) r) =
      twoPoint a (-s * r) := by
  have h := contractKernel_twoPoint_ratio (plusKernel s) a (fun _ => false) r 1 (-s)
    (by rfl) (by simp [plusKernel])
  simpa using h

lemma same_block_plus_true (a : ι → Bool) (r s : AlgebraicComplex) (hs : s ≠ 0) :
    contractKernel (plusKernel s) (twoPoint (Sum.elim a (fun _ => true)) r) =
      (-s) • twoPoint a (-r / s) := by
  have h := contractKernel_twoPoint_ratio (plusKernel s) a (fun _ => true) r (-s) (-s⁻¹)
    (by rfl) (by simp [plusKernel, hs])
  convert h using 1 <;> simp [div_eq_mul_inv, mul_comm]

lemma same_block_plus_wrong_xor (a : ι → Bool) (p : Bool → Bool)
    (hp : p false ≠ p true) (r s : AlgebraicComplex) :
    contractKernel (plusKernel s) (twoPoint (Sum.elim a p) r) = 0 := by
  rw [contractKernel_twoPoint]
  have hn : (!(p false)) ≠ (!(p true)) := fun h => hp (Bool.not_injective h)
  simp [plusKernel, hp, hn]

lemma same_block_minus_forward (a : ι → Bool) (r s : AlgebraicComplex) :
    contractKernel (minusKernel s) (twoPoint (Sum.elim a (fun b => b)) r) =
      twoPoint a (-s * r) := by
  have h := contractKernel_twoPoint_ratio (minusKernel s) a (fun b => b) r 1 (-s)
    (by rfl) (by simp [minusKernel])
  simpa using h

lemma same_block_minus_backward (a : ι → Bool) (r s : AlgebraicComplex) (hs : s ≠ 0) :
    contractKernel (minusKernel s) (twoPoint (Sum.elim a (fun b => !b)) r) =
      (-s) • twoPoint a (-r / s) := by
  have h := contractKernel_twoPoint_ratio (minusKernel s) a (fun b => !b) r (-s) (-s⁻¹)
    (by rfl) (by simp [minusKernel, hs])
  convert h using 1 <;> simp [div_eq_mul_inv, mul_comm]

lemma same_block_minus_wrong_xor (a : ι → Bool) (p : Bool → Bool)
    (hp : p false = p true) (r s : AlgebraicComplex) :
    contractKernel (minusKernel s) (twoPoint (Sum.elim a p) r) = 0 := by
  rw [contractKernel_twoPoint]
  simp [minusKernel, hp]

lemma twoPoint_nullary [IsEmpty ι] (a : ι → Bool) (r : AlgebraicComplex) :
    twoPoint a r = fun _ => 1 + r := by
  funext x
  have h0 : x = a := Subsingleton.elim _ _
  have h1 : x = fun i => !(a i) := Subsingleton.elim _ _
  change (if x = a then (1 : AlgebraicComplex) else 0) +
    r * (if x = (fun i => !(a i)) then 1 else 0) = 1 + r
  rw [if_pos h0, if_pos h1, mul_one]

end
end Paper2.HeightOne.PhaseCards
