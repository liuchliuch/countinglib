import Paper2.DegreeCSP.AxisRatioSigns
import Paper2.Tractable.Product

/-! Literal coefficient reconstruction of a full-support product table.
Every equality factor must join a coordinate to itself; disequality factors
are excluded by full support. Remaining unary factors are collected at their
original ports, retaining repetitions and the actual nullary scale. -/
namespace Paper2.DegreeCSP.FullSupportProduct
open scoped BigOperators
open Tractable AxisRatioSigns
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def factorUnary {n : ℕ} (h : ProductFactor n) (i : Fin n) (b : Bool) : AlgebraicComplex :=
  match h with
  | .unary j u _ => if i=j then u b else 1
  | .equality _ _ => 1
  | .disequality _ _ => 1

theorem factor_separated {n : ℕ} (h : ProductFactor n)
    (hh : ∀ x, h.eval x ≠ 0) (x : Fin n → Bool) :
    h.eval x = ∏ i, factorUnary h i (x i) := by
  classical
  cases h with
  | unary j u hu => simp [ProductFactor.eval,factorUnary]
  | equality j l =>
    have hjl : j=l := by
      by_contra hn
      have h := hh (Function.update zeroWord j true)
      simp [ProductFactor.eval,Signature.equality,Function.update,zeroWord,Ne.symm hn] at h
    subst l
    simp [ProductFactor.eval,factorUnary,Signature.equality]
  | disequality j l =>
    have h := hh zeroWord
    simp [ProductFactor.eval,Signature.disequality,zeroWord] at h

def collected {n : ℕ} (hs : List (ProductFactor n)) (i : Fin n) (b : Bool) : AlgebraicComplex :=
  (hs.map (fun h => factorUnary h i b)).prod

theorem list_separated {n : ℕ} (hs : List (ProductFactor n))
    (hh : ∀ h ∈ hs, ∀ x, h.eval x ≠ 0) (x : Fin n → Bool) :
    (hs.map (fun h => h.eval x)).prod = ∏ i, collected hs i (x i) := by
  classical
  induction hs with
  | nil => simp [collected]
  | cons h hs ih =>
    have hh0 := hh h List.mem_cons_self
    have hhs : ∀ g ∈ hs,∀ x,g.eval x≠0 :=
      fun g hg => hh g (List.mem_cons_of_mem h hg)
    simp only [List.map_cons,List.prod_cons,factor_separated h hh0 x,ih hhs]
    simp only [collected,List.map_cons,List.prod_cons]
    rw [Finset.prod_mul_distrib]

private theorem list_member_ne_zero (xs : List AlgebraicComplex) (hp : xs.prod≠0) :
    ∀ a∈xs,a≠0 := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have hax := mul_ne_zero_iff.mp hp
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact hax.1
    · exact ih hax.2 b hb

theorem unary_factorization {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : Product f) (hne : ∀ x,f x≠0) :
    ∃ (c : AlgebraicComplex) (u : Fin n → Bool → AlgebraicComplex),
      c≠0 ∧ (∀ i b,u i b≠0) ∧ ∀ x,f x=c*∏ i,u i (x i) := by
  classical
  rcases hf with hz | ⟨c,hc,hs,rfl⟩
  · exact False.elim (hne zeroWord (congrFun hz zeroWord))
  · have hh : ∀ h ∈ hs,∀ x,h.eval x≠0 := by
      intro h hm x
      have hp : (hs.map (fun h => h.eval x)).prod≠0 :=
        (mul_ne_zero_iff.mp (hne x)).2
      exact list_member_ne_zero _ hp (h.eval x) (List.mem_map.mpr ⟨h,hm,rfl⟩)
    have he (x : Fin n→Bool) : productFormula c hs x=c*∏ i,collected hs i (x i) := by
      unfold productFormula
      rw [list_separated hs hh x]
    refine ⟨c,collected hs,hc,?_,he⟩
    intro i b
    have hp : (∏ j,collected hs j ((fun _ : Fin n=>b) j))≠0 :=
      (mul_ne_zero_iff.mp (by simpa only [he] using hne (fun _=>b))).2
    exact Finset.prod_ne_zero_iff.mp hp i (Finset.mem_univ i)

theorem normalized {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : Product f) (hne : ∀ x,f x≠0) :
    ∀ x,f x=f zeroWord*wordFactor (axisRatio f) x := by
  classical
  obtain ⟨c,u,hc,hu,hf⟩ := unary_factorization f hf hne
  let φ : Fin n → AlgebraicComplex := fun i => u i true/u i false
  have huform (i : Fin n) (b : Bool) :
      u i b=u i false*(if b then φ i else 1) := by
    cases b
    · simp
    · simp only [ite_true,φ]
      exact (mul_div_cancel₀ _ (hu i false)).symm
  have hform (x : Fin n→Bool) : f x=f zeroWord*wordFactor φ x := by
    have hp : (∏ i,u i (x i)) = ∏ i,u i false*(if x i then φ i else 1) :=
      Finset.prod_congr rfl (fun i _ => huform i (x i))
    have hz : f zeroWord=c*∏ i,u i false := by simpa only [zeroWord] using hf zeroWord
    rw [hf x,hp,hz]
    rw [Finset.prod_mul_distrib]
    unfold wordFactor
    ring
  have hφ (i : Fin n) : axisRatio f i=φ i := by
    unfold axisRatio
    rw [hform]
    have hw : wordFactor φ (Function.update zeroWord i true)=φ i := by
      simp [wordFactor,Function.update,zeroWord]
    rw [hw]
    exact mul_div_cancel_left₀ _ (hne _)
  intro x
  have hφfun : axisRatio f=φ := funext hφ
  rw [hφfun]
  exact hform x

end
end Paper2.DegreeCSP.FullSupportProduct
