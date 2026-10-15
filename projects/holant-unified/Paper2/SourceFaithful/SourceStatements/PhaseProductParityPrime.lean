import Paper2.HeightOne.Dihedral.QuaternaryPrime

/-! A complementary-pair tensor has a genuine obstruction to every positive
ordered bipartition. This proves the primality converse without a group,
realizability, or card provider hypothesis. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable HeightOne.PhaseCards
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

lemma bool_complement_distinct {n : ℕ} (hn : 0 < n) (a : Fin n → Bool) :
    a ≠ fun i => !(a i) := by
  intro h
  have hi := congrFun h ⟨0,hn⟩
  cases ha : a ⟨0,hn⟩ <;> simp [ha] at hi

theorem tensorPrime_twoPoint {n : ℕ} (hn : 0 < n) (a : Fin n → Bool)
    (p δ : AlgebraicComplex) (hp : p ≠ 0) (hδ : δ ≠ 0) :
    TensorPrime (fun x => p * twoPoint a δ x) := by
  classical
  let abar : Fin n → Bool := fun i => !(a i)
  let f : Signature AlgebraicComplex n := fun x => p * twoPoint a δ x
  have ha : a ≠ abar := bool_complement_distinct hn a
  have hfa : f a = p := by simp [f,twoPoint,point,abar,ha]
  have hfb : f abar = p * δ := by simp [f,twoPoint,point,abar,ha.symm]
  refine ⟨?_,?_⟩
  · intro hz
    have := congrFun hz a
    change f a = 0 at this
    rw [hfa] at this
    exact hp this
  · intro m k hm hk e u v he
    have hvalue (x : Fin n → Bool) :
        u (fun i => x (e (Fin.castAdd k i))) *
          v (fun j => x (e (Fin.natAdd m j))) = f x := congrFun he x
    have hua : u (fun i => a (e (Fin.castAdd k i))) ≠ 0 := by
      have h := hvalue a
      rw [hfa] at h
      intro hu
      rw [hu,zero_mul] at h
      exact hp h.symm
    have hvb : v (fun j => abar (e (Fin.natAdd m j))) ≠ 0 := by
      have h := hvalue abar
      rw [hfb] at h
      intro hv
      rw [hv,mul_zero] at h
      exact (mul_ne_zero hp hδ) h.symm
    let mixed : Fin n → Bool := fun t =>
      Sum.elim (fun i => a (e (Fin.castAdd k i)))
        (fun j => abar (e (Fin.natAdd m j)))
        (finSumFinEquiv.symm (e.symm t))
    have hleft (i : Fin m) : mixed (e (Fin.castAdd k i)) = a (e (Fin.castAdd k i)) := by
      simp [mixed]
    have hright (j : Fin k) : mixed (e (Fin.natAdd m j)) = abar (e (Fin.natAdd m j)) := by
      simp [mixed]
    have hma : mixed ≠ a := by
      intro h
      have hx := congrFun h (e (Fin.natAdd m ⟨0,hk⟩))
      rw [hright] at hx
      change (!(a (e (Fin.natAdd m ⟨0,hk⟩)))) = a (e (Fin.natAdd m ⟨0,hk⟩)) at hx
      cases a (e (Fin.natAdd m ⟨0,hk⟩)) <;> simp at hx
    have hmb : mixed ≠ abar := by
      intro h
      have hx := congrFun h (e (Fin.castAdd k ⟨0,hm⟩))
      rw [hleft] at hx
      change a (e (Fin.castAdd k ⟨0,hm⟩)) = (!(a (e (Fin.castAdd k ⟨0,hm⟩)))) at hx
      cases a (e (Fin.castAdd k ⟨0,hm⟩)) <;> simp at hx
    have hzero : f mixed = 0 := by simp [f,twoPoint,point,hma,hmb,abar]
    have hnonzero : f mixed ≠ 0 := by
      rw [←hvalue mixed]
      simpa only [hleft,hright] using mul_ne_zero hua hvb
    exact hnonzero hzero

theorem source_5_13_prime_converse (a : Fin 4 → Bool) (p δ : AlgebraicComplex)
    (hp : p ≠ 0) (hδ : δ ≠ 0) :
    TensorPrime (fun x => p * twoPoint a δ x) :=
  tensorPrime_twoPoint (by decide) a p δ hp hδ

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity

