import Paper2.HeightOne.Cyclic.QuaternaryFourier
import Paper2.NetworkRealization

/-! Selecting two equal support bits requires only an ordered port
permutation and, when their common bit is true, exchanging the names of the
two support words. No bit-flip signature is introduced. -/
namespace Paper2.SourceFaithful.SourceStatements.TwoPointWalsh
open Paper2.Tractable Paper2.HeightOne.PhaseCards Paper2.EndpointSelfLoop
noncomputable section
set_option backward.isDefEq.respectTransparency false

def twoPointForm {ι : Type} [Fintype ι] (a : ι → Bool) (c0 c1 : AlgebraicComplex) :
    Tensor AlgebraicComplex ι :=
  fun x => c0 * point a x + c1 * point (fun i => !(a i)) x

lemma point_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (a : ι → Bool) :
    Tensor.reindex e (point a : Tensor AlgebraicComplex ι) = point (fun j => a (e.symm j)) := by
  classical
  funext x
  have he : (fun i => x (e i)) = a ↔ x = fun j => a (e.symm j) := by
    constructor
    · intro h
      funext j
      simpa using congrFun h (e.symm j)
    · intro h
      funext i
      simpa using congrFun h (e i)
  simp only [Tensor.reindex,point,he]

lemma twoPointForm_reindex {ι κ : Type} [Fintype ι] [Fintype κ] (e : ι ≃ κ) (a : ι → Bool)
    (c0 c1 : AlgebraicComplex) :
    Tensor.reindex e (twoPointForm a c0 c1) = twoPointForm (fun j => a (e.symm j)) c0 c1 := by
  have hp := point_reindex e a
  have hc := point_reindex e (fun i => !(a i))
  funext x
  exact congrArg₂ (fun u v : AlgebraicComplex => c0*u+c1*v) (congrFun hp x) (congrFun hc x)

lemma twoPointForm_complement {ι : Type} [Fintype ι] (a : ι → Bool) (c0 c1 : AlgebraicComplex) :
    twoPointForm a c0 c1 = twoPointForm (fun i => !(a i)) c1 c0 := by
  funext x
  simp [twoPointForm,add_comm]

lemma equal_support_ports {n : ℕ} (hn : 3 ≤ n) (a : Fin n → Bool) :
    ∃ i j : Fin n, i ≠ j ∧ a i = a j := by
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  let l : Fin n := ⟨2,by omega⟩
  by_cases hij : a i = a j
  · exact ⟨i,j,by simp [i,j,Fin.ext_iff],hij⟩
  by_cases hil : a i = a l
  · exact ⟨i,l,by simp [i,l,Fin.ext_iff],hil⟩
  refine ⟨j,l,by simp [j,l,Fin.ext_iff],?_⟩
  cases hi : a i <;> cases hj : a j <;> cases hl : a l <;> simp_all

def exposePair {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    Fin n ≃ Fin (Fintype.card (Remaining i j)+2) :=
  (splitPorts i j hij).trans (NetworkRealizable.frontPair (Remaining i j)).symm

@[simp] lemma exposePair_first {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (exposePair i j hij).symm 0 = i := by
  simp [exposePair,NetworkRealizable.frontPair,splitPorts]

@[simp] lemma exposePair_second {n : ℕ} (i j : Fin n) (hij : i ≠ j) :
    (exposePair i j hij).symm 1 = j := by
  simp only [exposePair,Equiv.symm_trans_apply,Equiv.symm_symm,
    NetworkRealizable.frontPair,Equiv.coe_fn_mk]
  rw [show (1 : Fin (Fintype.card (Remaining i j)+2)) =
    (0 : Fin (Fintype.card (Remaining i j)+1)).succ by rfl,Fin.cases_succ,Fin.cases_zero]
  rfl

/-- The two original coefficients are merely renamed. The phase-order
certificate is preserved when their ratio is inverted. -/
theorem orient_even_twoPoint {n : ℕ} (hn : 4 ≤ n) (he : Even n)
    (a : Fin n → Bool) (c0 c1 : AlgebraicComplex) (hc0 : c0 ≠ 0) (hc1 : c1 ≠ 0)
    (ell : ℕ) (hr : (c1/c0)^ell = 1) :
    ∃ (m : ℕ) (e : Fin n ≃ Fin (m+2)) (b : Fin (m+2) → Bool)
      (d0 d1 : AlgebraicComplex),
      2 ≤ m ∧ Even m ∧ b 0 = false ∧ b 1 = false ∧ d0 ≠ 0 ∧ d1 ≠ 0 ∧
      (d1/d0)^ell = 1 ∧ Tensor.reindex e (twoPointForm a c0 c1) = twoPointForm b d0 d1 := by
  obtain ⟨i,j,hij,ha⟩ := equal_support_ports (by omega) a
  let m := Fintype.card (Remaining i j)
  let e := exposePair i j hij
  have hm : m+2=n := by simpa [m] using remaining_card i j hij
  have hm2 : 2 ≤ m := by omega
  have hem : Even m := by
    obtain ⟨t,ht⟩ := he
    exact ⟨t-1,by omega⟩
  let b := fun p => a (e.symm p)
  have hb0 : b 0 = a i := by simp [b,e]
  have hb1 : b 1 = a j := by simp [b,e]
  have hform := twoPointForm_reindex e a c0 c1
  cases hbit : a i
  · exact ⟨m,e,b,c0,c1,hm2,hem,hb0.trans hbit,hb1.trans (ha.symm.trans hbit),
      hc0,hc1,hr,hform⟩
  · have hinv : c0/c1 = (c1/c0)⁻¹ := by field_simp
    refine ⟨m,e,(fun p => !(b p)),c1,c0,hm2,hem,?_,?_,hc1,hc0,?_,?_⟩
    · simp [hb0,hbit]
    · simp [hb1,← ha,hbit]
    · rw [hinv,inv_pow,hr,inv_one]
    · exact hform.trans (twoPointForm_complement b c0 c1)

end
end Paper2.SourceFaithful.SourceStatements.TwoPointWalsh
