import Paper2.DegreeCSP.GeneratedRestrictions
import Paper2.DegreeCSP.GeneratedCompose
import Paper2.DegreeCSP.PlainCubeFace
import Paper2.DegreeCSP.OrthogonalityScaling

/-! A actual two-copy Gram of a generated three-coordinate sign table. Its
nonzero scalar is retained and cancelled only in the proved BO invariant. -/
namespace Paper2.DegreeCSP
open scoped BigOperators
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace GeneratedSignQuadratic

def gram (f : Signature AlgebraicComplex 3) : Signature AlgebraicComplex 4 :=
  fun x=>∑b:Bool,f ![x 0,x 1,b]*f ![x 2,x 3,b]

private theorem generated_gram {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    {f : Signature AlgebraicComplex 3} (hf : Generated F k f) :
    Generated F k (gram f) := by
  have h := generated_sum_last (generated_hadamard
    (generated_pullback hf (![0,1,4] : Fin 3→Fin 5))
    (generated_pullback hf (![2,3,4] : Fin 3→Fin 5)))
  have he : (fun x : Fin 4→Bool=>∑b:Bool,
      f (fun i=>Fin.snoc (α:=fun _=>Bool) x b (![0,1,4] i))*
      f (fun i=>Fin.snoc (α:=fun _=>Bool) x b (![2,3,4] i)))=gram f := by
    funext x
    apply Finset.sum_congr rfl
    intro b _
    congr 2 <;> funext i <;> fin_cases i <;> rfl
  rw [he] at h
  exact h

/-- Every coefficient, including the common scalar, comes from the actual
hidden sum. The table is flattened on its first coordinate by a real pullback. -/
theorem scaled_gram_bo {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (f : Signature AlgebraicComplex 3) (hf : Generated F k f)
    (c : ℂ) (hc : c≠0) (P : (Fin 3→Bool)→ZMod 2)
    (hform : ∀x,(f x : ℂ)=c*BadCubeGram.sign (P x)) :
    OriginalBO.BlockOrthogonal (fun (row : Fin 3→Bool) (a : Bool)=>
      BadCubeGram.gram P ![a,row 0,row 1,row 2]) := by
  have hg := generated_gram hf
  have hr := generated_pullback hg (![3,0,1,2] : Fin 4→Fin 4)
  have hb := hBO 3 _ hr
  have hcoef (x : Fin 4→Bool) : (gram f x : ℂ)=c^2*BadCubeGram.gram P x := by
    simp only [gram,BadCubeGram.gram,Fintype.sum_bool]
    push_cast
    rw [hform ![x 0,x 1,true],hform ![x 2,x 3,true],
      hform ![x 0,x 1,false],hform ![x 2,x 3,false]]
    ring
  apply (OriginalBO.block_orthogonal_scale (c^2) (pow_ne_zero 2 hc) _).mp
  convert hb using 1
  funext row a
  have he : (fun i=>Fin.snoc (α:=fun _=>Bool) row a (![3,0,1,2] i))=
      ![a,row 0,row 1,row 2] := by
    funext i
    fin_cases i <;> rfl
  change c^2*BadCubeGram.gram P ![a,row 0,row 1,row 2]=_
  simp only [OriginalBO.tableRows,he]
  exact (hcoef ![a,row 0,row 1,row 2]).symm

/-- Every three-coordinate fixed face is a real generated table. A genuinely
nonquadratic sign would make its actual Gram violate the BO hypothesis. -/
theorem quadratic {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (g : Signature AlgebraicComplex n) (hg : Generated F k g)
    (hp0 : Generated F k (literalPin false)) (hp1 : Generated F k (literalPin true))
    (c : ℂ) (hc : c≠0) (P : (Fin n→Bool)→ZMod 2)
    (hform : ∀x,(g x : ℂ)=c*BadCubeGram.sign (P x)) :
    BooleanQuadratic.Quadratic P := by
  classical
  refine ⟨BooleanQuadratic.polynomial P,BooleanQuadratic.reconstruct P ?_⟩
  by_contra hn
  obtain ⟨z,i,j,l,hd,hbad⟩ := BadCubeGram.nonquadratic_plain_gram_witness P hn
  let r : Fin n→Option (Fin 3) := fun q=>
    if q=i then some 0 else if q=j then some 1 else if q=l then some 2 else none
  let f : Signature AlgebraicComplex 3 := fun x=>
    g (Function.update (Function.update (Function.update z i (x 0)) j (x 1)) l (x 2))
  have hf : Generated F k f := by
    have h := generated_restrict hg hp0 hp1 r z
    rcases h with ⟨R,hR,hdiv,hvalue⟩
    refine ⟨R,hR,hdiv,?_⟩
    rw [hvalue]
    funext x
    congr 1
    funext q
    rcases hd with ⟨hij,hjl,hil⟩
    by_cases hqi:q=i
    · subst q; simp [r,Function.update,hij,hil]
    by_cases hqj:q=j
    · subst q; simp [r,Function.update,hqi,hjl]
    by_cases hql:q=l
    · subst q; simp [r,Function.update,hqi,hqj]
    · simp [r,Function.update,hqi,hqj,hql]
  apply hbad
  apply scaled_gram_bo hBO f hf c hc (BadCubeGram.plainFace P z i j l)
  intro x
  exact hform _

end GeneratedSignQuadratic
end
end Paper2.DegreeCSP
