import Paper2.DegreeCSP.FullSupportSigns
import Paper2.DegreeCSP.GeneratedUnaryRestrictions
import Paper2.DegreeCSP.GeneratedUnaryPhases

/-! Actual unary restrictions and seven retained copies remove eighth-root
axis phases. The resulting sign table keeps its actual nonzero scalar. -/
namespace Paper2.DegreeCSP
open scoped BigOperators
open Tractable TensorDecomposition AxisRatioSigns
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace GeneratedPhaseRemoval

private theorem generated_prod {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    {ι : Type} [Fintype ι] (g : ι → Signature AlgebraicComplex n)
    (hg : ∀ i,Generated F k (g i)) : Generated F k (fun x=>∏ i,g i x) := by
  classical
  have h : ∀ s : Finset ι,Generated F k (fun x=>∏i∈s,g i x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (generated_one (F:=F) (k:=k) (n:=n))
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using generated_hadamard (hg i) ih
  simpa using h Finset.univ

private theorem axis_value {n : ℕ} (f : Signature AlgebraicComplex n)
    (hne : f zeroWord ≠ 0) (i : Fin n) (b : Bool) :
    f (Function.update zeroWord i b)=f zeroWord*(if b then axisRatio f i else 1) := by
  cases b
  · have he : Function.update zeroWord i false=(zeroWord : Fin n→Bool) := by
      funext j
      by_cases hji:j=i
      · subst j; simp [Function.update,zeroWord]
      · exact Function.update_of_ne hji false zeroWord
    simp [he]
  · simp only [ite_true,axisRatio]
    exact (mul_div_cancel₀ _ hne).symm

/-- Each selected axis is a literal generated unary restriction. -/
theorem axis_eighth {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (A : Signature AlgebraicComplex 2) (hA : Generated F k A)
    (a u v : ℂ) (ha : a≠0) (hu : u≠0) (hv : v≠0)
    (hchart : ∀ b c,(A ![b,c] : ℂ)=OriginalBO.phaseChart a u v b c)
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (hp : Generated F k (literalPin false)) (hne : ∀ x,f x≠0) :
    ∀ i,axisRatio f i^8=1 := by
  intro i
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let g : Signature AlgebraicComplex 1 := fun z=>f (Function.update zeroWord i (z 0))
    have hg : Generated F k g := generated_unary_axis hf hp i
    have h0 : g ![false]≠0 := hne _
    have h1 : g ![true]≠0 := hne _
    have he := GeneratedUnaryPhases.eighth hBO A hA a u v ha hu hv hchart g hg h0 h1
    have hgf : g ![false]=f zeroWord := by
      dsimp [g]
      simpa only [Bool.false_eq_true,ite_false,mul_one] using axis_value f (hne _) i false
    have hh : (g ![true]/g ![false])^8=1 := by exact_mod_cast he
    simpa only [axisRatio,g,hgf,Matrix.cons_val_zero] using hh

/-- The normalized sign has zero constant and zero single-coordinate terms. -/
theorem sign_axis_zero {n : ℕ} (f : Signature AlgebraicComplex n)
    (hne : ∀x,f x≠0) (P : (Fin n→Bool)→Bool)
    (hform : ∀x,f x=f zeroWord*(∏j,if x j then axisRatio f j else 1)*
      (if P x then -1 else 1)) :
    ∀ i,P (Function.update zeroWord i true)=false := by
  classical
  intro i
  have he := hform (Function.update zeroWord i true)
  have hw : (∏j,if Function.update zeroWord i true j then axisRatio f j else 1)=
      axisRatio f i := by
    simp [Function.update,zeroWord]
  rw [hw,axis_value f (hne _) i true] at he
  have hz := mul_ne_zero (hne zeroWord) (axisRatio_ne_zero f hne i)
  cases hp : P (Function.update zeroWord i true)
  · rfl
  · simp only [hp,ite_true,mul_neg,mul_one] at he
    have htwice : (2 : AlgebraicComplex)*(f zeroWord*axisRatio f i)=0 := by
      linear_combination he
    exact False.elim ((mul_ne_zero (by norm_num) hz) htwice)

/-- No scalar is silently deleted: the displayed table is genuinely generated. -/
theorem signs {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (hp : Generated F k (literalPin false)) (hne : ∀ x,f x≠0)
    (hphase : ∀ i,axisRatio f i ^ 8=1) :
    ∃ (P : (Fin n→Bool)→Bool) (c : AlgebraicComplex),c≠0 ∧ P zeroWord=false ∧
      Generated F k (fun x=>c*(if P x then -1 else 1)) ∧
      (∀ x,f x=f zeroWord*(∏i,if x i then axisRatio f i else 1)*
        (if P x then -1 else 1)) := by
  obtain ⟨_,P,hP,hform⟩ := generated_full_support_signs hBO f hf hne
  let g : Fin n → Signature AlgebraicComplex n := fun i x=>
    f (Function.update zeroWord i (x i))^7
  have hg (i : Fin n) : Generated F k (g i) := by
    cases n with
    | zero => exact Fin.elim0 i
    | succ n =>
      have hu := generated_unary_axis hf hp i
      have h := generated_pow (generated_pullback hu (fun _ : Fin 1=>i)) 7
      exact h
  have hM := generated_hadamard hf (generated_prod g hg)
  let c : AlgebraicComplex := f zeroWord*(∏i:Fin n,f zeroWord^7)
  have hc : c≠0 := mul_ne_zero (hne _) (Finset.prod_ne_zero_iff.mpr (by
    intro i _
    exact pow_ne_zero 7 (hne _)))
  have he : (fun x=>f x*∏i,g i x)=(fun x=>c*(if P x then -1 else 1)) := by
    funext x
    have hi (i : Fin n) : (if x i then axisRatio f i else 1)*g i x=f zeroWord^7 := by
      dsimp [g]
      rw [axis_value f (hne _) i (x i)]
      cases hxi:x i
      · simp
      · simp only [ite_true,mul_pow]
        calc
          axisRatio f i*(f zeroWord^7*axisRatio f i^7)=
              f zeroWord^7*(axisRatio f i^8) := by ring
          _=f zeroWord^7 := by rw [hphase i,mul_one]
    calc
      f x*∏i,g i x =
          f zeroWord*(if P x then -1 else 1)*
            ((∏i,if x i then axisRatio f i else 1)*(∏i,g i x)) := by rw [hform x]; ring
      _=f zeroWord*(if P x then -1 else 1)*
            (∏i,(if x i then axisRatio f i else 1)*g i x) := by rw [Finset.prod_mul_distrib]
      _=c*(if P x then -1 else 1) := by simp only [hi]; dsimp [c]; ring
  rw [he] at hM
  exact ⟨P,c,hc,hP,hM,hform⟩

end GeneratedPhaseRemoval
end
end Paper2.DegreeCSP
