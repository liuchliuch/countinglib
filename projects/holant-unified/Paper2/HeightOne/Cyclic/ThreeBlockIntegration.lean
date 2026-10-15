import Paper2.HeightOne.Cyclic.SameBlockMinors
import Paper2.HeightOne.Cyclic.LogicalSlices

/-! The six-port cyclic case. Three actual phases kill all six logical face
minors, so the full eight-coefficient cube factors without an exceptional κ. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable EndpointSelfLoop
open scoped BigOperators

abbrev cubeWord {r : ℕ} (e : Fin r ≃ Fin 3) (t : Fin 3 → Bool) : Fin r → Bool := fun k => t (e k)

lemma cubeWord_update {r : ℕ} (e : Fin r ≃ Fin 3) (t : Fin 3 → Bool) (i : Fin 3) (b : Bool) :
    Function.update (cubeWord e t) (e.symm i) b = cubeWord e (Function.update t i b) := by
  classical
  funext k
  by_cases hk : k = e.symm i
  · subst k
    simp [cubeWord]
  · have he : e k ≠ i := fun h => hk (e.symm_apply_eq.mpr h.symm).symm
    simp [cubeWord, hk, he]

lemma vec3_update_zero (a b c v : Bool) : Function.update ![a,b,c] 0 v = ![v,b,c] := by
  funext k; fin_cases k <;> simp
lemma vec3_update_one (a b c v : Bool) : Function.update ![a,b,c] 1 v = ![a,v,c] := by
  funext k; fin_cases k <;> simp
lemma vec3_update_two (a b c v : Bool) : Function.update ![a,b,c] 2 v = ![a,b,v] := by
  funext k; fin_cases k <;> simp

lemma cubeWord_rectangle {r : ℕ} (e : Fin r ≃ Fin 3) (x y z w : Fin 3 → Bool)
    (h : PortRectangle x y z w) : PortRectangle (cubeWord e x) (cubeWord e y) (cubeWord e z) (cubeWord e w) :=
  fun k => h (e k)

/-- The exact six face equations in the original logical cube. -/
theorem three_block_faces {n : ℕ} (f : Signature AlgebraicComplex n) (P : Pairing n)
    (hF : support f ⊆ equalityCode P) (e : Fin P.count ≃ Fin 3)
    (s t u : AlgebraicComplex) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hmatch : ∀ a b (hab : a ≠ b), ∀ q, q = s ∨ q = t ∨ q = u →
      plusContraction a b hab q f ≠ 0 → EqualityMatchingSupport (plusContraction a b hab q f))
    (hprod : ∀ a b (hab : a ≠ b), ∀ q, q = s ∨ q = t ∨ q = u →
      Product (Tensor.reindex (Fintype.equivFin (Remaining a b)) (plusContraction a b hab q f))) :
    Dihedral.cubeFacesZero (fun a b c => f (blockWord P (cubeWord e ![a,b,c]))) := by
  have H (i : Fin 3) (x y z w : Fin 3 → Bool) (hr : PortRectangle x y z w) (b : Bool) :=
    same_block_endpoint_rectangles f P hF (e.symm i) s t u hst hsu htu
      (hmatch _ _ _) (hprod _ _ _) (cubeWord e x) (cubeWord e y) (cubeWord e z) (cubeWord e w)
      (cubeWord_rectangle e x y z w hr) b
  refine ⟨?_, ?_, ?_⟩
  · intro b
    have h := H 2 ![false,false,false] ![true,true,false] ![false,true,false] ![true,false,false]
      (by intro k; fin_cases k <;> simp [PortRectangle]) b
    apply sub_eq_zero.mpr
    simpa only [cubeWord_update, vec3_update_two] using h
  · intro b
    have h := H 1 ![false,false,false] ![true,false,true] ![false,false,true] ![true,false,false]
      (by intro k; fin_cases k <;> simp [PortRectangle]) b
    apply sub_eq_zero.mpr
    simpa only [cubeWord_update, vec3_update_one] using h
  · intro b
    have h := H 0 ![false,false,false] ![false,true,true] ![false,false,true] ![false,true,false]
      (by intro k; fin_cases k <;> simp [PortRectangle]) b
    apply sub_eq_zero.mpr
    simpa only [cubeWord_update, vec3_update_zero] using h

/-- Three logical blocks factor just as the larger cubes do. In this branch
no Paper 1 diagonal-integration parameter is required. -/
theorem logical_three_factorization {n : ℕ} (f : Signature AlgebraicComplex n) (P : Pairing n)
    (hP : P.count = 3) (hF : support f ⊆ equalityCode P) (h0 : f (fun _ => false) ≠ 0)
    (s t u : AlgebraicComplex) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hmatch : ∀ a b (hab : a ≠ b), ∀ q, q = s ∨ q = t ∨ q = u →
      plusContraction a b hab q f ≠ 0 → EqualityMatchingSupport (plusContraction a b hab q f))
    (hprod : ∀ a b (hab : a ≠ b), ∀ q, q = s ∨ q = t ∨ q = u →
      Product (Tensor.reindex (Fintype.equivFin (Remaining a b)) (plusContraction a b hab q f))) :
    ∃ ρ : Fin P.count → AlgebraicComplex, (∀ i, ρ i ≠ 0) ∧
      ∀ x, f (blockWord P x) = f (fun _ => false) * ∏ i, (if x i then ρ i else 1) := by
  let e : Fin P.count ≃ Fin 3 := finCongr hP
  let c : Bool → Bool → Bool → AlgebraicComplex := fun a b c => f (blockWord P (cubeWord e ![a,b,c]))
  have hfull := logical_full_support f P (by omega) hF h0 s (fun a b hab => hmatch a b hab s (Or.inl rfl))
  have hn : ∀ a b d, c a b d ≠ 0 := fun a b d => hfull _
  have hfaces := three_block_faces f P hF e s t u hst hsu htu hmatch hprod
  have he := Dihedral.cube_factorization_of_faces c hn hfaces
  let ρ : Fin P.count → AlgebraicComplex := fun k =>
    ![c true false false / c false false false, c false true false / c false false false,
      c false false true / c false false false] (e k)
  have hρ : ∀ i, ρ i ≠ 0 := by
    intro i
    unfold ρ
    generalize e i = j
    fin_cases j <;> exact div_ne_zero (hn _ _ _) (hn _ _ _)
  refine ⟨ρ, hρ, ?_⟩
  intro x
  let y : Fin 3 → Bool := fun j => x (e.symm j)
  have hx : cubeWord e ![y 0, y 1, y 2] = x := by
    funext k
    have hy : ![y 0, y 1, y 2] = y := by funext j; fin_cases j <;> rfl
    rw [hy]
    simp [cubeWord, y]
  have hz : c false false false = f (fun _ => false) := by
    have hv : (![false,false,false] : Fin 3 → Bool) = (fun _ => false) := by
      funext k; fin_cases k <;> rfl
    change f (blockWord P (cubeWord e ![false,false,false])) = _
    rw [hv]
  have hprod' : (∏ i, if x i then ρ i else 1) =
      (if y 0 then c true false false / c false false false else 1) *
      (if y 1 then c false true false / c false false false else 1) *
      (if y 2 then c false false true / c false false false else 1) := by
    rw [← e.symm.prod_comp (fun i => if x i then ρ i else 1)]
    simp [ρ, y, Fin.prod_univ_succ, mul_assoc]
  have h := he (y 0) (y 1) (y 2)
  change f (blockWord P (cubeWord e ![y 0,y 1,y 2])) = _ at h
  rw [hx, hz] at h
  rw [hprod']
  simpa only [hz, mul_assoc] using h

end
end Paper2.HeightOne.Cyclic
