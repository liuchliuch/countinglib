import ComplexCSP.Structure.WeightedMaltsevPinnedLayer
import ComplexCSP.Complexity.CSPMarginalCacheBounds

/-! # Original-instance bit bounds for the pinned layer implementation -/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness ComplexityWitnessEncoding
open ComplexityCSPMarginalRowBounds ComplexityCSPMarginalCacheBounds ComplexityWitnessSizeBounds
open PlanarHom PlanarHom.Complexity PlanarHom.MachineComposition
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}

omit [Algebra ℚ K] in
theorem buildPinnedLayer_label_realized {n : ℕ} {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : MaltsevWitness.Code (Fin d) (n+1)} (G : (Fin (n+1) → Fin d) → K)
    (hW : Correct W {x | G x ≠ 0}) (hEq : PreservesRowEquivalence m (rowFiber G))
    (evaluate : Tuple (Fin d) (n+1) → K) (he : ∀ x, evaluate x = G (view x))
    (defaultValue : Fin d) (entry : RowLabel K d × StoredCode d n)
    (hentry : entry ∈ buildPinnedLayer m W evaluate defaultValue) :
    ∃ a ∈ rowSupport G, tableLabel G a = entry.1 := by
  have hP : Correct (projectCode W n (Nat.le_succ n)) (rowSupport G) := by
    simpa only [projection_rowSupport] using projectCode_correct hW n (Nat.le_succ n)
  have hl := rowLabel_correct evaluate G he
  have hEq' : PreservesRowEquivalence m (labelFiber (rowSupport G) (rowLabel evaluate)) := by
    rw [hl,labelFiber_rowFiber]; exact hEq
  have hR := row_equivalence_support_preserves hEq'
  have hmemb : entry.1 ∈ (splitPinnedTypeClasses m (projectCode W n (Nat.le_succ n))
      (rowLabel evaluate) defaultValue).map Prod.fst := List.mem_map.mpr ⟨entry,hentry,rfl⟩
  obtain ⟨a,ha,hlabel⟩ := (splitPinnedTypeClasses_labels hm hR hP (rowLabel evaluate) hEq' defaultValue entry.1).mp hmemb
  exact ⟨a,ha,by simpa only [hl,view_ofFn] using hlabel⟩

/-- Every actual pinned layer has a uniform original-instance bit bound. The
finite witness storage, class count and factor sizes are all independently
proved; no output-size premise is supplied to the constructor. -/
theorem exists_buildPinnedLayer_output_bound (L : Language (Fin d) K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) : ∃ p : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code), ComplexityCSPCode.Valid L g →
    ∀ (k : ℕ) (hk1 : k+1 ≤ g.vertices) (m : Operation (Fin d)), IsMaltsev m →
    ∀ (W : MaltsevWitness.Code (Fin d) (k+1)),
      Correct W {x | ComplexityCSPMarginalBounds.marginal L g hk1 x ≠ 0} →
      PreservesRowEquivalence m (rowFiber (ComplexityCSPMarginalBounds.marginal L g hk1)) →
    ∀ (evaluate : Tuple (Fin d) (k+1) → K),
      (∀ x, evaluate x = ComplexityCSPMarginalBounds.marginal L g hk1 (view x)) →
    ∀ (defaultValue : Fin d) (σ : K →+* ℂ),
      BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) x a)) →
      ((ComplexityWeightedLayers.layerCode basis).encode
        (encodeLayer (buildPinnedLayer m W evaluate defaultValue))).length ≤
          p.eval (ComplexityCSPCode.encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_normalized_marginal_bounds L basis
  refine ⟨(Polynomial.C 6*(Polynomial.C (2*d)+Polynomial.C 2*p+storedPolynomial d+2)+3)*
    Polynomial.C d+1,?_⟩
  intro g hg k hk1 m hm W hW hEq evaluate he defaultValue σ hBO
  let N := (ComplexityCSPCode.encoding.encode g).length
  have hkN : k ≤ N := by
    have h := ComplexityCSPCode.size_le_encoding_length g
    omega
  have hlen := buildPinnedLayer_length_le hm _ hW hEq evaluate he defaultValue σ hBO
  have hfactor : ∀ e ∈ buildPinnedLayer m W evaluate defaultValue,
      ((numberFieldEncoding basis).encode (labelFactor e.1)).length ≤ p.eval N := by
    intro e hee
    obtain ⟨a,_,ha⟩ := buildPinnedLayer_label_realized hm _ hW hEq evaluate he defaultValue e hee
    rw [← ha]
    exact (hp g hg k hk1 a).2
  have hb := encodeLayer_bound basis _ (p.eval N) hlen hfactor
  have hs := natPolynomial_monotone (storedPolynomial d) hkN
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one,
    Polynomial.eval_ofNat]
  change _ ≤ (6*(2*d+2*p.eval N+(storedPolynomial d).eval N+2)+3)*d+1
  nlinarith

end ComplexCSP.WeightedMaltsev
