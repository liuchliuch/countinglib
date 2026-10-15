import Paper2.HeightOne.Cyclic.BalancedTables

/-! Exact odd-root dressing of the two cyclic quaternary RN families. The
chosen phases are applied through the already proved native attachment graph;
only the final displayed scalar normalization is analytic. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhaseCards PhasePencil Dihedral
open scoped BigOperators

@[simp] lemma mkRoot_value {N : ℕ} [NeZero N] (a : AlgebraicComplex) (h : a ^ N = 1) :
    ((rootsOfUnity.mkOfPowEq a h).val : AlgebraicComplex) = a := rfl

def rootWeighted {N : ℕ} (r : Fin 4 → rootsOfUnity N AlgebraicComplex)
    (q : Signature AlgebraicComplex 4) : Signature AlgebraicComplex 4 :=
  fun x => ((rootWeight r x).val : AlgebraicComplex) * q x

lemma rootWeighted_even {N : ℕ} (r : Fin 4 → rootsOfUnity N AlgebraicComplex)
    (q : Signature AlgebraicComplex 4) (hq : SupportedOnParity q 0) :
    SupportedOnParity (rootWeighted r q) 0 := by
  intro x hx
  apply hq x
  intro hz
  apply hx
  simp [rootWeighted,hz]

/-- Every live-endpoint family has actual dressing phases making its endpoint
coefficients equal and every live complementary central pair equal to -p. -/
theorem live_family_dressing_phases {N : ℕ} (hodd : Odd N)
    (q : Signature AlgebraicComplex 4) (heven : SupportedOnParity q 0)
    (hp : q (fun _ => false) ≠ 0)
    (hrows : QuaternaryRows N (q (fun _ => false)) (q (fun _ => true))
      (fun i => q (centralWord i (fun _ => false)))
      (fun i => q (flipAll (centralWord i (fun _ => false))))) :
    ∃ (r : Fin 4 → rootsOfUnity N AlgebraicComplex) (s : Fin 3 → AlgebraicComplex),
      (∀ i, s i = 0 ∨ s i = -q (fun _ => false)) ∧
      rootWeighted r q = balancedWalsh (q (fun _ => false)) s := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hodd.pos⟩
  obtain ⟨lambda,hlambda,ht,hdata⟩ := shared_cyclic_live hodd.pos hp hrows
  choose alpha halpha hpair using hdata
  let R : rootsOfUnity N AlgebraicComplex := (rootsOfUnity.mkOfPowEq lambda hlambda)⁻¹
  let A : Fin 3 → rootsOfUnity N AlgebraicComplex :=
    fun i => rootsOfUnity.mkOfPowEq (alpha i) (halpha i)
  obtain ⟨r,hR,hu,hv⟩ := prescribe_four_port_phases hodd R
    (fun i => A i * R)
  let s : Fin 3 → AlgebraicComplex :=
    fun i => if q (centralWord i (fun _ => false)) = 0 then 0 else -q (fun _ => false)
  have hlamnz := root_ne_zero hodd.pos hlambda
  have hanz : ∀ i, alpha i ≠ 0 := fun i => root_ne_zero hodd.pos (halpha i)
  have hRval : ((rootWeight r (fun _ => true)).val : AlgebraicComplex) = lambda⁻¹ := by
    rw [hR]
    simp [R,rootsOfUnity.mkOfPowEq]
  have huval (i : Fin 3) :
      ((rootWeight r (centralWord i (fun _ => false))).val : AlgebraicComplex) = alpha i / lambda := by
    rw [hu]
    simp [A,R,div_eq_mul_inv,rootsOfUnity.mkOfPowEq]
  have hvval (i : Fin 3) :
      ((rootWeight r (flipAll (centralWord i (fun _ => false)))).val : AlgebraicComplex) = (alpha i)⁻¹ := by
    rw [hv]
    simp [A,R,rootsOfUnity.mkOfPowEq]
  refine ⟨r,s,?_,?_⟩
  · intro i
    dsimp only [s]
    split_ifs <;> simp
  · apply balancedWalsh_of_values
    · exact rootWeighted_even r q heven
    · simp [rootWeighted,rootWeight_zero]
    · rw [rootWeighted,hRval,ht]
      field_simp [hlamnz]
    · intro i
      change (rootWeight r (centralWord i (fun _ => false))).val *
        q (centralWord i (fun _ => false)) = s i
      rw [huval]
      rcases hpair i with hzero | hlive
      · simp [s,hzero.1]
      · have hxne : q (centralWord i (fun _ => false)) ≠ 0 := by
          rw [hlive.1]
          exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hp) hlamnz) (hanz i)
        simp only [s,if_neg hxne,hlive.1]
        field_simp [hlamnz,hanz i]
        <;> ring
    · intro i
      change (rootWeight r (flipAll (centralWord i (fun _ => false)))).val *
        q (flipAll (centralWord i (fun _ => false))) = s i
      rw [hvval]
      rcases hpair i with hzero | hlive
      · simp [s,hzero.1,hzero.2]
      · have hxne : q (centralWord i (fun _ => false)) ≠ 0 := by
          rw [hlive.1]
          exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr hp) hlamnz) (hanz i)
        simp only [s,if_neg hxne,hlive.2]
        field_simp [hlamnz,hanz i]
        <;> ring

/-- A zero-endpoint family is dressed into three equal complementary pairs.
The chosen square roots lie in the same actual odd root group. -/
theorem zero_family_dressing_phases {N : ℕ} (hodd : Odd N)
    (q : Signature AlgebraicComplex 4) (heven : SupportedOnParity q 0)
    (hzero : q (fun _ => false) = 0) (hone : q (fun _ => true) = 0)
    (hrows : QuaternaryRows N 0 0
      (fun i => q (centralWord i (fun _ => false)))
      (fun i => q (flipAll (centralWord i (fun _ => false))))) :
    ∃ (r : Fin 4 → rootsOfUnity N AlgebraicComplex) (s : Fin 3 → AlgebraicComplex),
      (∀ i, s i = 0 ↔ q (centralWord i (fun _ => false)) = 0) ∧
      rootWeighted r q = balancedWalsh 0 s := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hodd.pos⟩
  choose alpha halpha hpair using shared_cyclic_zero hodd.pos hrows
  let A : Fin 3 → rootsOfUnity N AlgebraicComplex :=
    fun i => rootsOfUnity.mkOfPowEq (alpha i) (halpha i)
  let beta : Fin 3 → rootsOfUnity N AlgebraicComplex := fun i => A i ^ ((N + 1) / 2)
  have hb (i : Fin 3) : beta i ^ 2 = A i := odd_root_half_power hodd (A i)
  have hbval (i : Fin 3) : ((beta i).val : AlgebraicComplex) ^ 2 = alpha i := by
    have h := congrArg (fun z : rootsOfUnity N AlgebraicComplex => (z.val : AlgebraicComplex)) (hb i)
    push_cast at h
    simpa [A,rootsOfUnity.mkOfPowEq] using h
  have hbnz (i : Fin 3) : ((beta i).val : AlgebraicComplex) ≠ 0 := Units.ne_zero _
  obtain ⟨r,hR,hu,hv⟩ := prescribe_four_port_phases hodd 1 beta
  let s : Fin 3 → AlgebraicComplex := fun i => (beta i).val * q (centralWord i (fun _ => false))
  have huval (i : Fin 3) :
      ((rootWeight r (centralWord i (fun _ => false))).val : AlgebraicComplex) = (beta i).val := by
    rw [hu]
  have hvval (i : Fin 3) :
      ((rootWeight r (flipAll (centralWord i (fun _ => false)))).val : AlgebraicComplex) =
        ((beta i).val : AlgebraicComplex)⁻¹ := by
    rw [hv]
    simp
  refine ⟨r,s,?_,?_⟩
  · intro i
    exact mul_eq_zero_iff_left (hbnz i)
  · apply balancedWalsh_of_values
    · exact rootWeighted_even r q heven
    · simp [rootWeighted,hzero]
    · simp [rootWeighted,hone]
    · intro i
      simp only [rootWeighted,huval]
      rfl
    · intro i
      simp only [rootWeighted,hvval,hpair]
      rw [← hbval i]
      dsimp only [s]
      field_simp
      <;> ring

/-- Dressing phases are realized by four actual binary attachments over F,
with their nonzero product scale kept in the displayed Walsh table. -/
theorem actual_dressing_balanced {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (C : RotationCards F N) (f : Signature AlgebraicComplex 4)
    (hf : NetworkRealizable F f) (r : Fin 4 → rootsOfUnity N AlgebraicComplex)
    (p : AlgebraicComplex) (s : Fin 3 → AlgebraicComplex)
    (he : rootWeighted r (walshCoordinates f) = balancedWalsh p s) :
    ∃ (h : Signature AlgebraicComplex 4) (c : AlgebraicComplex),
      NetworkRealizable F h ∧ c ≠ 0 ∧
      walshCoordinates h = fun x => c * balancedWalsh p s x := by
  obtain ⟨h,c,hr,hc,hw⟩ := actual_four_port_dressing C f hf r
  refine ⟨h,c,hr,hc,?_⟩
  rw [hw]
  funext x
  have h := congrFun he x
  rw [rootWeighted,coe_rootWeight] at h
  rw [← h]
  ring

end
end Paper2.HeightOne.Cyclic
