import Paper2.DegreeCSP.TwoWordContextDegrees

/-! Positive literal pin/edge multiplicities for the original two-word
contexts. At degree modulus one, a single pin/edge fixes each hidden bit. -/
namespace Paper2.DegreeCSP.OriginalContextCommonPhase
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

def copies (k : ℕ) : ℕ := if k = 1 then 1 else k - 1

theorem copies_pos {k : ℕ} (hk : 0 < k) : 0 < copies k := by
  unfold copies
  split_ifs <;> omega

theorem copies_eq {k : ℕ} (hk : k ≠ 1) : copies k = k - 1 := ite_eq_right hk

def rowContext {n : ℕ} (x y : Fin n → Bool) (f : Signature AlgebraicComplex n) (k : ℕ) :
    Presentation AlgebraicComplex (Fin 1) := TwoWordContext.context x y f (copies k)

theorem rowContext_hidden {n k : ℕ} (hk : 0 < k) (x y : Fin n → Bool)
    (f : Signature AlgebraicComplex n) : PartialUnaryProducts.HiddenDivisible (rowContext x y f k) k := by
  by_cases h1 : k = 1
  · subst k
    exact fun _ => one_dvd _
  · simpa only [rowContext, copies_eq h1] using TwoWordContext.hidden_divisible x y f hk

theorem rowContext_value {n k : ℕ} (hk : 0 < k) (x y : Fin n → Bool)
    (f : Signature AlgebraicComplex n) (b : Bool) :
    (rowContext x y f k).value (fun _ => b) = f (if b then y else x) :=
  TwoWordContext.value x y f (copies_pos hk) b

theorem rowContext_value_false {n k : ℕ} (hk : 0 < k) (x y : Fin n → Bool)
    (f : Signature AlgebraicComplex n) : (rowContext x y f k).value ![false] = f x := by
  have he : (![false] : Fin 1 → Bool) = (fun _ => false) := by
    funext i
    fin_cases i
    rfl
  rw [he, rowContext_value hk]
  rfl

theorem rowContext_value_true {n k : ℕ} (hk : 0 < k) (x y : Fin n → Bool)
    (f : Signature AlgebraicComplex n) : (rowContext x y f k).value ![true] = f y := by
  have he : (![true] : Fin 1 → Bool) = (fun _ => true) := by
    funext i
    fin_cases i
    rfl
  rw [he, rowContext_value hk]
  rfl

theorem rowContext_degree {n : ℕ} (x y : Fin n → Bool)
    (f : Signature AlgebraicComplex n) (k : ℕ) :
    (rowContext x y f k).degree (Sum.inl 0) = TwoWordContext.boundaryCount x y (copies k) :=
  TwoWordContext.boundary_degree x y f (copies k)

/-- Changing the actual pin count at modulus one does not alter the phase
equation because the common phase is then exactly one. -/
theorem requested_exponent {n k : ℕ} (x y : Fin n → Bool)
    {θ v : AlgebraicComplex} (hθ : θ ^ k = 1)
    (hv : v = θ ^ TwoWordContext.boundaryCount x y (copies k)) :
    v = θ ^ TwoWordContext.boundaryCount x y (k - 1) := by
  by_cases h1 : k = 1
  · have he : θ = 1 := by simpa only [h1, pow_one] using hθ
    simpa only [he, one_pow] using hv
  · simpa only [copies_eq h1] using hv

end
end Paper2.DegreeCSP.OriginalContextCommonPhase
