import Paper2.HeightOne.Cyclic.QuaternaryPhases

/-! The complete eight-coefficient balanced table, with all four original
ports retained. Even support is the only support premise in reconstruction. -/
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhaseCards Dihedral
open scoped BigOperators

lemma balancedWalsh_zero (p : AlgebraicComplex) (s : Fin 3 → AlgebraicComplex) :
    balancedWalsh p s (fun _ => false) = p := by
  simp [balancedWalsh,point,centralWord,flipPair,flipAll,Fin.sum_univ_three,
    funext_iff,Fin.forall_fin_succ]

lemma balancedWalsh_one (p : AlgebraicComplex) (s : Fin 3 → AlgebraicComplex) :
    balancedWalsh p s (fun _ => true) = p := by
  simp [balancedWalsh,point,centralWord,flipPair,flipAll,Fin.sum_univ_three,
    funext_iff,Fin.forall_fin_succ]

lemma balancedWalsh_central (p : AlgebraicComplex) (s : Fin 3 → AlgebraicComplex)
    (i : Fin 3) : balancedWalsh p s (centralWord i (fun _ => false)) = s i := by
  fin_cases i <;> simp [balancedWalsh,point,centralWord,flipPair,flipAll,Fin.sum_univ_three,
    funext_iff,Fin.forall_fin_succ]

lemma balancedWalsh_complement (p : AlgebraicComplex) (s : Fin 3 → AlgebraicComplex)
    (i : Fin 3) : balancedWalsh p s (flipAll (centralWord i (fun _ => false))) = s i := by
  fin_cases i <;> simp [balancedWalsh,point,centralWord,flipPair,flipAll,Fin.sum_univ_three,
    funext_iff,Fin.forall_fin_succ]

lemma balancedWalsh_even (p : AlgebraicComplex) (s : Fin 3 → AlgebraicComplex) :
    SupportedOnParity (balancedWalsh p s) 0 := by
  intro x hx
  by_contra hp
  have hz : balancedWalsh p s x = 0 := by
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
    all_goals simp only [parity,Paper2.weight,Fin.sum_univ_four,
      h0,h1,h2,h3,Bool.false_eq_true,if_false,if_true] at hp
    all_goals norm_num at hp
    all_goals simp [balancedWalsh,point,centralWord,flipPair,flipAll,Fin.sum_univ_three,
      funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]
  exact hx hz

lemma balancedWalsh_of_values (q : Signature AlgebraicComplex 4)
    (p : AlgebraicComplex) (s : Fin 3 → AlgebraicComplex)
    (heven : SupportedOnParity q 0) (hzero : q (fun _ => false) = p)
    (hone : q (fun _ => true) = p)
    (hcentral : ∀ i, q (centralWord i (fun _ => false)) = s i)
    (hcomplement : ∀ i, q (flipAll (centralWord i (fun _ => false))) = s i) :
    q = balancedWalsh p s := by
  funext x
  by_cases hp : parity x = 0
  · have hz : parity (fun _ : Fin 4 => false) = 0 := by simp [parity,Paper2.weight]
    rcases parity_word_cover (fun _ => false) x (hp.trans hz.symm) with h | h | ⟨i,h⟩ | ⟨i,h⟩
    · rw [h,hzero,balancedWalsh_zero]
    · change x = (fun _ => true) at h
      rw [h,hone,balancedWalsh_one]
    · rw [h,hcentral,balancedWalsh_central]
    · rw [h,hcomplement,balancedWalsh_complement]
  · have hq : q x = 0 := by by_contra hx; exact hp (heven x hx)
    have hb : balancedWalsh p s x = 0 := by
      by_contra hx
      exact hp (balancedWalsh_even p s x hx)
    rw [hq,hb]

/-- At sum zero, inverse Walsh exchanges the six central coefficients with
four times themselves. This is a literal table identity, not an added gadget. -/
lemma inverseWalsh_zero_sum (s : Fin 3 → AlgebraicComplex) (hs : ∑ i, s i = 0) :
    action walsh (balancedWalsh 0 s) = balancedWalsh 0 (fun i => 4 * s i) := by
  apply balancedWalsh_of_values
  · exact inverseWalsh_balanced_even 0 s
  · rw [inverseWalsh_balanced_zero,hs]; ring
  · rw [inverseWalsh_balanced_one,hs]; ring
  · intro i
    rw [inverseWalsh_balanced_central,hs]; ring
  · intro i
    rw [inverseWalsh_balanced_central_complement,hs]; ring

end
end Paper2.HeightOne.Cyclic
