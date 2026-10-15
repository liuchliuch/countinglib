import Paper2.HeightOne.Dihedral.HighArityActual

/-! Exact original-port correspondence between the actual Paper 2 xor cards
and the inherited-card convention used by the proved matching surgery. -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Tractable PhaseCards EndpointSelfLoop GroupSplit
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

private theorem remaining_lower_bound {n : ℕ} (p : Equiv.Perm (Fin (n+2)))
    (z : Remaining (p 0) (p 1)) : 2 ≤ (p.symm z.val).val := by
  have h0 : p.symm z.val ≠ 0 := by
    intro h
    apply z.property.1
    simpa only [Equiv.apply_symm_apply] using congrArg p h
  have h1 : p.symm z.val ≠ 1 := by
    intro h
    apply z.property.2
    simpa only [Equiv.apply_symm_apply] using congrArg p h
  have hv0 : (p.symm z.val).val ≠ 0 := fun h => h0 (Fin.ext h)
  have hv1 : (p.symm z.val).val ≠ 1 := by
    intro h
    apply h1
    apply Fin.ext
    simpa only [Fin.val_one,Nat.mod_eq_of_lt (by omega : 1 < n+2)] using h
  omega

def orderedRemaining {n : ℕ} (p : Equiv.Perm (Fin (n+2))) :
    Fin n ≃ Remaining (p 0) (p 1) where
  toFun j := ⟨p j.succ.succ,by
    constructor
    · intro h
      exact Fin.succ_ne_zero j.succ (p.injective h)
    · intro h
      exact Fin.succ_succ_ne_one j (p.injective h)⟩
  invFun z := ⟨(p.symm z.val).val - 2,by
    have h := (p.symm z.val).isLt
    have hb := remaining_lower_bound p z
    omega⟩
  left_inv j := by
    apply Fin.ext
    simp only [Equiv.symm_apply_apply,Fin.val_succ]
    omega
  right_inv z := by
    apply Subtype.ext
    apply p.symm.injective
    simp only [Equiv.symm_apply_apply]
    apply Fin.ext
    simp only [Fin.val_succ]
    have hb := remaining_lower_bound p z
    omega

theorem ordered_extendBits {n : ℕ} (p : Equiv.Perm (Fin (n+2)))
    (a b : Bool) (x : Fin n → Bool) :
    extendBits (p 0) (p 1) (p.injective.ne Fin.zero_ne_one)
      (fun z => x ((orderedRemaining p).symm z)) a b =
      fun i => (Fin.cons a (Fin.cons b x) : Fin (n+2) → Bool) (p.symm i) := by
  classical
  funext i
  obtain ⟨j,rfl⟩ := p.surjective i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j
  · simp [extendBits,splitPorts]
  · simp [extendBits,splitPorts]
  · have h0 : p k.succ.succ ≠ p 0 := p.injective.ne (Fin.succ_ne_zero k.succ)
    have h1 : p k.succ.succ ≠ p 1 := p.injective.ne (Fin.succ_succ_ne_one k)
    have hsplit : splitPorts (p 0) (p 1) (p.injective.ne Fin.zero_ne_one)
        (p k.succ.succ) = Sum.inl ⟨p k.succ.succ,h0,h1⟩ := by
      simp [splitPorts,h0,h1]
    change Sum.elim (fun z => x ((orderedRemaining p).symm z))
      (fun t => if t then b else a)
      (splitPorts (p 0) (p 1) (p.injective.ne Fin.zero_ne_one) (p k.succ.succ)) = _
    rw [hsplit]
    simp only [Sum.elim_inl,Equiv.symm_apply_apply,Fin.cons_succ]
    have hz : (⟨p k.succ.succ,h0,h1⟩ : Remaining (p 0) (p 1)) = orderedRemaining p k := rfl
    rw [hz,Equiv.symm_apply_apply]

theorem ordered_card {n : ℕ} (p : Equiv.Perm (Fin (n+2)))
    (C : Kernel AlgebraicComplex) (f : Signature AlgebraicComplex (n+2)) :
    Tensor.reindex (orderedRemaining p).symm
      (card C (p 0) (p 1) (p.injective.ne Fin.zero_ne_one) f) =
      Holant.Signature.contract C (Tensor.reindex p.symm f) := by
  funext x
  calc
    _ = ∑ v : Bool × Bool,C v.1 v.2 * f
        (extendBits (p 0) (p 1) (p.injective.ne Fin.zero_ne_one)
          (fun z => x ((orderedRemaining p).symm z)) v.1 v.2) := by
      unfold Tensor.reindex card contractKernel
      apply Fintype.sum_equiv (Equiv.boolArrowEquivProd Bool)
      intro v
      congr 1
      congr 1
      funext i
      cases i with
      | inl j => rfl
      | inr c => cases c <;> rfl
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp only [ordered_extendBits,Holant.Signature.contract,Tensor.reindex]

theorem xorKernel_negative_M (v : Bool) (s : AlgebraicComplex) :
    xorKernel false v s = Holant.Dihedral.CompatibleClosure.M v (-s) := by
  funext a b
  cases a <;> cases b <;> cases v <;>
    simp [xorKernel,Holant.Dihedral.CompatibleClosure.M,Holant.Marked.monomial]

theorem minimum_ordered_xor_matching {F : SignatureFamily AlgebraicComplex}
    {N n : ℕ} [NeZero N] (C : XorCards F N) (L : ExactInput.Language)
    (heven : ∀ f ∈ L.family,Even f.1) (hsafe : AllBinariesSafe L.family)
    (hG : actualClasses L.family = dihedralPhaseClasses N)
    (hmin : LeastPrimeArity L.family (n+2)) (f : Signature AlgebraicComplex (n+2))
    (hprocessed : (xorMenu C).Processed ⟨n+2,f⟩ L)
    (p : Equiv.Perm (Fin (n+2))) (v : Bool) (s : rootsOfUnity N AlgebraicComplex) :
    Holant.Certificates.MatchingContractionClosure.MatchingOrZero monomialGroup
      (Holant.Signature.contract (Holant.Dihedral.CompatibleClosure.M v (-s.val))
        (Tensor.reindex p.symm (walshCoordinates f))) := by
  have hh := minimum_xorCard_matching C L heven hsafe hG hmin f hprocessed
    (p 0) (p 1) (p.injective.ne Fin.zero_ne_one) false v s
  have hi := hh.reindex (Fintype.equivFin (Remaining (p 0) (p 1))).symm
  have he : Holant.Tensor.reindex (Fintype.equivFin (Remaining (p 0) (p 1))).symm
      (Tensor.reindex (Fintype.equivFin (Remaining (p 0) (p 1)))
        (card (xorKernel false v s.val) (p 0) (p 1)
          (p.injective.ne Fin.zero_ne_one) (walshCoordinates f))) =
      card (xorKernel false v s.val) (p 0) (p 1)
        (p.injective.ne Fin.zero_ne_one) (walshCoordinates f) := by
    funext x
    simp only [Holant.Tensor.reindex,Tensor.reindex,Equiv.symm_apply_apply]
  rw [he] at hi
  have ho := hi.reindex (orderedRemaining p).symm
  rw [← xorKernel_negative_M]
  rw [← ordered_card p]
  exact ho

end
end Paper2.HeightOne.Dihedral.HighArity
