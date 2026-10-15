import Paper2.HeightOne.PhaseCards.WalshTransport

/-! Finite Walsh characters, including the exact unnormalized orthogonality
factor. These are coordinate identities, with no realizability assertion. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace Paper2.SourceFaithful.SourceStatements.TwoPointWalshPair
noncomputable section
open Paper2.Tractable Paper2.HeightOne.PhaseCards
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {ι : Type} [Fintype ι]

def delta (a x : ι → Bool) : AlgebraicComplex := if x = a then 1 else 0

def character (a x : ι → Bool) : AlgebraicComplex := ∏ i, walsh (x i) (a i)

def sign (a : ι → Bool) : AlgebraicComplex := ∏ i, if a i then -1 else 1

lemma action_delta (a : ι → Bool) : action walsh (delta a) = character a := by
  classical
  funext x
  simp [action,delta,character]

lemma action_linear (M : Kernel AlgebraicComplex) (c d : AlgebraicComplex)
    (f g : Tensor AlgebraicComplex ι) :
    action M (fun x => c * f x + d * g x) =
      fun x => c * action M f x + d * action M g x := by
  classical
  funext x
  simp only [action, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

lemma walsh_character (a : ι → Bool) : walshCoordinates (character a) = delta a := by
  rw [← action_delta,walsh_inv_action_cancel]

lemma walsh_ne_zero (a b : Bool) : walsh a b ≠ 0 := by
  cases a <;> cases b <;> norm_num [walsh]

lemma character_ne_zero (a x : ι → Bool) : character a x ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => walsh_ne_zero _ _)

lemma sign_ne_zero (a : ι → Bool) : sign a ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases a i <;> norm_num

lemma character_complement (a x : ι → Bool) :
    character a (fun i => !(x i)) = sign a * character a x := by
  classical
  rw [character,sign,character,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases a i <;> cases x i <;> norm_num [walsh]

lemma sign_complement (a : ι → Bool) :
    sign (fun i => !(a i)) = (-1 : AlgebraicComplex) ^ Fintype.card ι * sign a := by
  classical
  change _ = (-1 : AlgebraicComplex) ^ Finset.univ.card * sign a
  rw [← Finset.prod_const,sign,sign,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases a i <;> norm_num

lemma sum_character_mul (a b : ι → Bool) :
    (∑ x, character a x * character b x) =
      if a = b then (2 : AlgebraicComplex) ^ Fintype.card ι else 0 := by
  classical
  have hb (i : ι) : (∑ z : Bool, walsh z (a i) * walsh z (b i)) =
      if a i = b i then (2 : AlgebraicComplex) else 0 := by
    cases a i <;> cases b i <;> norm_num [walsh,Fintype.sum_bool]
  calc
    _ = ∑ x : ι → Bool, ∏ i, walsh (x i) (a i) * walsh (x i) (b i) := by
      simp only [character,Finset.prod_mul_distrib]
    _ = ∏ i, ∑ z : Bool, walsh z (a i) * walsh z (b i) :=
      (Fintype.prod_sum (fun (i : ι) (z : Bool) => walsh z (a i) * walsh z (b i))).symm
    _ = ∏ i, if a i = b i then (2 : AlgebraicComplex) else 0 := by simp only [hb]
    _ = _ := by
      by_cases h : a = b
      · subst b
        simp
      · rw [if_neg h]
        obtain ⟨i,hi⟩ := Function.ne_iff.mp h
        exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

end
end Paper2.SourceFaithful.SourceStatements.TwoPointWalshPair

