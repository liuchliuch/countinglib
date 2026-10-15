import Paper2.HeightOne.PhaseCards.Cards

/-! Every oriented xor sector is supplied by an actual phase or reflected
binary. Reversing the sector inverts the phase and retains its nonzero scalar;
the xor offsets below are analytic indices, never unproved gadget operations. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable GroupSplit GroupSplit.MatrixGroup EndpointSelfLoop
open scoped BigOperators

def xorKernel (u v : Bool) (s : AlgebraicComplex) : AMat := fun x y =>
  if x = u ∧ y = v then 1 else if x = !u ∧ y = !v then -s else 0

lemma xorKernel_false_false (s : AlgebraicComplex) :
    xorKernel false false s = plusKernel s := by
  funext x y
  cases x <;> cases y <;> rfl

lemma xorKernel_false_true (s : AlgebraicComplex) :
    xorKernel false true s = minusKernel s := by
  funext x y
  cases x <;> cases y <;> rfl

lemma xorKernel_reverse (v : Bool) (s : AlgebraicComplex) (hs : s ≠ 0) :
    xorKernel true v s = (-s) • xorKernel false (!v) s⁻¹ := by
  funext x y
  cases v <;> cases x <;> cases y <;>
    simp [xorKernel, hs]

/-- The complete actual dihedral group provides a literal representative of
each ordered xor kernel, including phases at the opposite orientation. -/
theorem actual_xor_card {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hN : 0 < N) (hG : actualClasses F = dihedralPhaseClasses N)
    (u v : Bool) (s : AlgebraicComplex) (hs : s ^ N = 1) :
    ∃ (B : AMat) (c : AlgebraicComplex), ActualNonsingular F B ∧ c ≠ 0 ∧
      analysisKernel B = c • xorKernel u v s := by
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  have hs0 : s ≠ 0 := by
    intro hz
    simp [hz, Nat.ne_of_gt hN] at hs
  have forward (v : Bool) (s : AlgebraicComplex) (hs : s ^ N = 1) :
      ∃ (B : AMat) (c : AlgebraicComplex), ActualNonsingular F B ∧ c ≠ 0 ∧
        analysisKernel B = c • xorKernel false v s := by
    let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs
    cases v
    · obtain ⟨B, c, hB, hc, he⟩ := actual_plus_card (Or.inr hG) r
      exact ⟨B, 2 * c, hB, mul_ne_zero (by norm_num) hc,
        by simpa only [xorKernel_false_false, r, rootsOfUnity.coe_mkOfPowEq] using he⟩
    · obtain ⟨B, c, hB, hc, he⟩ := actual_minus_card hG r
      exact ⟨B, -2 * c, hB, mul_ne_zero (by norm_num) hc,
        by simpa only [xorKernel_false_true, r, rootsOfUnity.coe_mkOfPowEq] using he⟩
  cases u
  · exact forward v s hs
  · have hi : (s⁻¹) ^ N = 1 := by rw [inv_pow, hs, inv_one]
    obtain ⟨B, c, hB, hc, he⟩ := forward (!v) s⁻¹ hi
    refine ⟨B, c / (-s), hB, div_ne_zero hc (neg_ne_zero.mpr hs0), ?_⟩
    rw [xorKernel_reverse v s hs0, smul_smul, div_mul_cancel₀ _ (neg_ne_zero.mpr hs0)]
    exact he

variable {ι : Type} [Fintype ι]

lemma card_kernel_sum (E : AMat) (a b : ι) (hab : a ≠ b)
    (f : Tensor AlgebraicComplex ι) (y : Remaining a b → Bool) :
    card E a b hab f y =
      ∑ u : Bool, ∑ v : Bool, E u v * f (extendBits a b hab y u v) := by
  unfold card contractKernel
  calc
    _ = ∑ p : Bool × Bool, E p.1 p.2 * f (extendBits a b hab y p.1 p.2) := by
      apply Fintype.sum_equiv (Equiv.boolArrowEquivProd Bool)
      intro v
      congr 1
      congr 1
      funext i
      cases i with
      | inl j => rfl
      | inr c => cases c <;> rfl
    _ = _ := Fintype.sum_prod_type _

lemma card_xor_apply (a b : ι) (hab : a ≠ b) (u v : Bool)
    (s : AlgebraicComplex) (f : Tensor AlgebraicComplex ι)
    (y : Remaining a b → Bool) :
    card (xorKernel u v s) a b hab f y =
      f (extendBits a b hab y u v) - s * f (extendBits a b hab y (!u) (!v)) := by
  rw [card_kernel_sum]
  cases u <;> cases v <;>
    simp [xorKernel, Fintype.sum_bool, sub_eq_add_neg, add_comm]

end
end Paper2.HeightOne.PhaseCards
