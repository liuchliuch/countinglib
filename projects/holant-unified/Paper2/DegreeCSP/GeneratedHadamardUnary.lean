import Paper2.DegreeCSP.GeneratedGram
import Paper2.DegreeCSP.HadamardUnaryPhase
import Paper2.DegreeCSP.GeneratedUnaryRestrictions
import Paper2.DegreeCSP.AxisRatioSigns

/-! Actual shared-boundary multiplication and a hidden Boolean Fourier sum
turn a genuinely generated Hadamard table into a fourth-root unary constraint. -/
namespace Paper2.DegreeCSP
open Tractable TensorDecomposition AxisRatioSigns
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace GeneratedHadamardUnary

def anchor (a : AlgebraicComplex) : Signature AlgebraicComplex 2 :=
  fun x=>a*(if x 0&&x 1 then -1 else 1)

def rowProduct (a : AlgebraicComplex) (g : Signature AlgebraicComplex 1) :
    Signature AlgebraicComplex 2 := fun x=>anchor a x*g ![x 0]

def fourier (a : AlgebraicComplex) (g : Signature AlgebraicComplex 1) :
    Signature AlgebraicComplex 1 := fun x=>∑b:Bool,anchor a ![x 0,b]*g ![b]

private theorem rowProduct_generated {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    {a : AlgebraicComplex} {g : Signature AlgebraicComplex 1}
    (ha : Generated F k (anchor a)) (hg : Generated F k g) :
    Generated F k (rowProduct a g) := by
  have h := generated_hadamard ha (generated_pullback hg (fun _ : Fin 1=>(0 : Fin 2)))
  have he : (fun x=>anchor a x*g (fun _ : Fin 1=>x 0))=rowProduct a g := by
    funext x
    congr 2
    funext i
    rw [Fin.eq_zero i]
    rfl
  rw [he] at h
  exact h

private theorem fourier_generated {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    {a : AlgebraicComplex} {g : Signature AlgebraicComplex 1}
    (ha : Generated F k (anchor a)) (hg : Generated F k g) :
    Generated F k (fourier a g) := by
  have h := generated_sum_last (generated_hadamard ha
    (generated_pullback hg (fun _ : Fin 1=>(1 : Fin 2))))
  have he : (fun x : Fin 1→Bool=>∑b:Bool,
      anchor a (Fin.snoc (α:=fun _=>Bool) x b)*
        g (fun _ : Fin 1=>Fin.snoc (α:=fun _=>Bool) x b 1))=fourier a g := by
    funext x
    apply Finset.sum_congr rfl
    intro b _
    congr 2
    · funext i; fin_cases i <;> rfl
    · funext i; rw [Fin.eq_zero i]; rfl
  rw [he] at h
  exact h

private theorem rowProduct_table (a : AlgebraicComplex) (g : Signature AlgebraicComplex 1)
    (b c : Bool) : (rowProduct a g ![b,c] : ℂ)=
      (a : ℂ)*HadamardUnaryPhase.table (g ![false] : ℂ) (g ![true] : ℂ) b c := by
  cases b <;> cases c <;> simp [rowProduct,anchor,HadamardUnaryPhase.table]

private theorem rowProduct_bo {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k) {a : AlgebraicComplex}
    (ha : a≠0) (hanchor : Generated F k (anchor a))
    (g : Signature AlgebraicComplex 1) (hg : Generated F k g) :
    OriginalBO.BlockOrthogonal (HadamardUnaryPhase.table (g ![false] : ℂ) (g ![true] : ℂ)) ∧
      OriginalBO.BlockOrthogonal (fun b c=>
        HadamardUnaryPhase.table (g ![false] : ℂ) (g ![true] : ℂ) c b) := by
  have hac : (a : ℂ)≠0 := by exact_mod_cast ha
  have hp := rowProduct_generated hanchor hg
  have h := OriginalBO.generated_binary_bo hBO (rowProduct a g) hp
  have ht := OriginalBO.generated_binary_transpose_bo hBO (rowProduct a g) hp
  constructor
  · apply (OriginalBO.block_orthogonal_scale (a : ℂ) hac _).mp
    convert h using 1
    funext b c
    exact (rowProduct_table a g b c).symm
  · apply (OriginalBO.block_orthogonal_scale (a : ℂ) hac _).mp
    convert ht using 1
    funext b c
    exact (rowProduct_table a g c b).symm

/-- The literal generated anchor and its genuine Fourier sum are both used. -/
theorem phase_four {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k) (a : AlgebraicComplex)
    (ha : a≠0) (hanchor : Generated F k (anchor a))
    (g : Signature AlgebraicComplex 1) (hg : Generated F k g)
    (h0 : g ![false]≠0) (h1 : g ![true]≠0) :
    ((g ![true] : ℂ)/(g ![false] : ℂ))^4=1 := by
  have h := rowProduct_bo hBO ha hanchor g hg
  have hF := rowProduct_bo hBO ha hanchor (fourier a g)
    (fourier_generated hanchor hg)
  have hf (b : Bool) : (fourier a g ![b] : ℂ)=
      (a : ℂ)*(if b then (g ![false] : ℂ)-(g ![true] : ℂ)
        else (g ![false] : ℂ)+(g ![true] : ℂ)) := by
    cases b <;> (simp [fourier,anchor]; ring)
  have hac : (a : ℂ)≠0 := by exact_mod_cast ha
  have hw : OriginalBO.BlockOrthogonal (HadamardUnaryPhase.table
      ((g ![false] : ℂ)+(g ![true] : ℂ)) ((g ![false] : ℂ)-(g ![true] : ℂ))) := by
    apply (OriginalBO.block_orthogonal_scale (a : ℂ) hac _).mp
    convert hF.1 using 1
    funext b c
    rw [hf false,hf true]
    cases b <;> cases c <;> simp [HadamardUnaryPhase.table]
    all_goals ring
  have hwt : OriginalBO.BlockOrthogonal (fun b c=>HadamardUnaryPhase.table
      ((g ![false] : ℂ)+(g ![true] : ℂ)) ((g ![false] : ℂ)-(g ![true] : ℂ)) c b) := by
    apply (OriginalBO.block_orthogonal_scale (a : ℂ) hac _).mp
    convert hF.2 using 1
    funext b c
    rw [hf false,hf true]
    cases b <;> cases c <;> simp [HadamardUnaryPhase.table]
    all_goals ring
  apply HadamardUnaryPhase.phase_four _ _ (by exact_mod_cast h0) (by exact_mod_cast h1)
    h.1 h.2 hw hwt

/-- Literal zero-pinned coordinate slices give every displayed axis phase. -/
theorem axis_phase_four {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k) (a : AlgebraicComplex)
    (ha : a≠0) (hanchor : Generated F k (anchor a))
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (hp : Generated F k (literalPin false)) (hne : ∀x,f x≠0) :
    ∀i,axisRatio f i^4=1 := by
  intro i
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    let g : Signature AlgebraicComplex 1 := fun z=>f (Function.update zeroWord i (z 0))
    have hg : Generated F k g := generated_unary_axis hf hp i
    have he := phase_four hBO a ha hanchor g hg (hne _) (hne _)
    have hh : (g ![true]/g ![false])^4=1 := by exact_mod_cast he
    have hzero : Function.update zeroWord i false=(zeroWord : Fin (n+1)→Bool) := by
      funext j
      by_cases hji:j=i
      · subst j; simp [Function.update,zeroWord]
      · exact Function.update_of_ne hji false zeroWord
    simpa only [axisRatio,g,Matrix.cons_val_zero,hzero] using hh

end GeneratedHadamardUnary
end
end Paper2.DegreeCSP
