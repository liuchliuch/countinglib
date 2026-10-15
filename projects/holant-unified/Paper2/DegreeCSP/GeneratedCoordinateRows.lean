import Paper2.DegreeCSP.GeneratedCompose

/-! Every coordinate can be the retained Boolean column of an actual generated
table. The boundary permutation changes no occurrence or degree. Consequently
the original BO assumption constrains any two coordinate rows and their square. -/
namespace Paper2.DegreeCSP.OriginalBO
open Paper2.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def coordinateRows {n : ℕ} (f : Signature AlgebraicComplex (n+1))
    (i : Fin (n+1)) (x : Fin (n+1) → Bool) (b : Bool) : ℂ :=
  (f (Function.update x i b) : ℂ)

/-- Read the remaining columns after literally swapping the chosen one with
the last coordinate. Reattaching b gives exactly the original word with i set. -/
theorem swap_snoc_update {n : ℕ} (i : Fin (n+1)) (x : Fin (n+1) → Bool) (b : Bool) :
    (fun j : Fin (n+1)=>Fin.snoc (α:=fun _=>Bool)
      (fun t : Fin n=>x ((Equiv.swap i (Fin.last n)).symm t.castSucc)) b
      ((Equiv.swap i (Fin.last n)) j)) = Function.update x i b := by
  classical
  let e := Equiv.swap i (Fin.last n)
  funext j
  by_cases hj : j=i
  · subst j
    simp [e]
  · have he : e j≠Fin.last n := by
      intro h
      apply hj
      apply e.injective
      exact h.trans (Equiv.swap_apply_left i (Fin.last n)).symm
    obtain ⟨t,ht⟩ := Fin.exists_castSucc_eq.mpr he
    change Fin.snoc (α:=fun _=>Bool) (fun t : Fin n=>x (e.symm t.castSucc)) b (e j) = Function.update x i b j
    rw [←ht,Fin.snoc_castSucc]
    rw [ht,e.symm_apply_apply,Function.update_of_ne hj]

theorem coordinate_rows_bo {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : AllGeneratedOriginalBO F k) (f : Signature AlgebraicComplex (n+1))
    (hf : Generated F k f) (i : Fin (n+1)) : BlockOrthogonal (coordinateRows f i) := by
  classical
  let e := Equiv.swap i (Fin.last n)
  let g : Signature AlgebraicComplex (n+1) := fun z=>f (fun j=>z (e j))
  have hg : Generated F k g := generated_reindex hf e
  have h := precompose_rows (hBO n g hg)
    (fun x : Fin (n+1)→Bool=>fun t : Fin n=>x (e.symm t.castSucc))
  convert h using 1
  funext x b
  change (f (Function.update x i b) : ℂ) =
    (f (fun j=>Fin.snoc (α:=fun _=>Bool) (fun t : Fin n=>x (e.symm t.castSucc)) b (e j)) : ℂ)
  rw [show (fun j=>Fin.snoc (α:=fun _=>Bool) (fun t : Fin n=>x (e.symm t.castSucc)) b (e j)) =
    Function.update x i b from swap_snoc_update i x b]

/-- Full-support generated tables obey the exact squared cross relation
between any two rows in any coordinate. The square is an actual generated
table, provided by the disjoint-product construction. -/
theorem squared_cross_rows {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : AllGeneratedOriginalBO F k) (f : Signature AlgebraicComplex (n+1))
    (hf : Generated F k f) (hne : ∀ x,f x≠0) (i : Fin (n+1))
    (x y : Fin (n+1)→Bool) :
    ((f (Function.update x i false) : ℂ)*(f (Function.update y i true) : ℂ))^2 =
      ((f (Function.update x i true) : ℂ)*(f (Function.update y i false) : ℂ))^2 := by
  let r : Bool → (Fin (n+1)→Bool) := fun b=>if b then y else x
  let G : Bool → Bool → ℂ := fun b c=>coordinateRows f i (r b) c
  have hG : BlockOrthogonal G := precompose_rows (coordinate_rows_bo hBO f hf i) r
  have hG2 : BlockOrthogonal (fun b c=>G b c^2) := by
    have h := precompose_rows (coordinate_rows_bo hBO (fun z=>f z^2) (generated_pow hf 2) i) r
    convert h using 1
    funext b c
    simp [G,coordinateRows]
  have hneG (b c : Bool) : G b c≠0 := by
    change (f (Function.update (r b) i c) : ℂ)≠0
    exact_mod_cast hne (Function.update (r b) i c)
  simpa only [G,r,coordinateRows,Bool.false_eq_true,ite_false,ite_true] using
    binary_squared_cross G hneG hG hG2

/-- The same identity holds in the original algebraic coefficient field. -/
theorem squared_cross_rows_algebraic {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : AllGeneratedOriginalBO F k) (f : Signature AlgebraicComplex (n+1))
    (hf : Generated F k f) (hne : ∀ x,f x≠0) (i : Fin (n+1))
    (x y : Fin (n+1)→Bool) :
    (f (Function.update x i false)*f (Function.update y i true))^2 =
      (f (Function.update x i true)*f (Function.update y i false))^2 := by
  exact_mod_cast squared_cross_rows hBO f hf hne i x y

end
end Paper2.DegreeCSP.OriginalBO
