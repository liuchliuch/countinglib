import Paper2.Paper1ProvedOddUnaryTwoWordDescent
import Paper2.Support

/-! The least positive occupied Hamming gap is chosen from the input table,
and forces a descended endpoint pair to have no intermediate support. -/
namespace Paper2.Paper1Proved.OddUnary.TwoWordDescent
open Paper2
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {n : ℕ}

theorem unequal_weights_of_not_singleLayer (f : Signature K n)
    (h : ¬∃ d, Signature.SingleLayer f d) :
    ∃ x y, f x≠0 ∧ f y≠0 ∧ weight x<weight y := by
  classical
  have hn : f≠0 := by
    intro zero
    apply h
    exact ⟨0,by simp [zero,Signature.SingleLayer]⟩
  obtain ⟨x,hx⟩ := Function.ne_iff.mp hn
  have other : ∃ y, f y≠0 ∧ weight y≠weight x := by
    by_contra no
    push Not at no
    apply h
    refine ⟨weight x,?_⟩
    intro y hy
    by_contra live
    exact hy (no y live)
  obtain ⟨y,hy,hxy⟩ := other
  rcases lt_or_gt_of_ne hxy with hlt|hlt
  · exact ⟨y,x,hy,hx,hlt⟩
  · exact ⟨x,y,hx,hy,hlt⟩

theorem least_occupied_gap (f : Signature K n)
    (h : ¬∃ d, Signature.SingleLayer f d) :
    ∃ d : ℕ, 0<d ∧ MinimumGap f d ∧
      ∃ x y, f x≠0 ∧ f y≠0 ∧ gap x y=(d : ℤ) := by
  classical
  let P : ℕ → Prop := fun d => 0<d ∧
    ∃ x y, f x≠0 ∧ f y≠0 ∧ gap x y=(d : ℤ)
  have existsP : ∃ d,P d := by
    obtain ⟨x,y,hx,hy,hxy⟩ := unequal_weights_of_not_singleLayer f h
    refine ⟨weight y-weight x,by omega,x,y,hx,hy,?_⟩
    dsimp [gap]
    omega
  let d := Nat.find existsP
  obtain ⟨positive,x,y,hx,hy,eq⟩ := Nat.find_spec existsP
  refine ⟨d,positive,?_,x,y,hx,hy,eq⟩
  intro a b ha hb hab
  have ab : weight a<weight b := by dsimp [gap] at hab; omega
  have small : d≤weight b-weight a := by
    apply Nat.find_min' existsP
    exact ⟨by omega,a,b,ha,hb,by dsimp [gap]; omega⟩
  dsimp [gap]
  omega

theorem endpoint_only_of_minimumGap (f : Signature K n)
    (hd : MinimumGap f n) (hzero : f (fun _=>false)≠0)
    (x : Fin n → Bool) (hx : x≠fun _=>false) (hx' : x≠fun _=>true) : f x=0 := by
  by_contra live
  have pos : 0<weight x := by
    apply Nat.pos_of_ne_zero
    intro zero
    exact hx ((weight_eq_zero_iff x).mp zero)
  have bound := weight_le x
  have lower := hd (fun _=>false) x hzero live (by simp [gap]; exact_mod_cast pos)
  have eq : weight x=n := by simp only [gap,weight_false,Nat.cast_zero,sub_zero] at lower; omega
  exact hx' ((weight_eq_card_iff x).mp (by simpa using eq))

theorem endpoints_gap : gap (fun _ : Fin n=>false) (fun _=>true)=(n : ℤ) := by
  simp [gap]

end
end Paper2.Paper1Proved.OddUnary.TwoWordDescent
