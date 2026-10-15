import Paper2.SourceFaithful.SourceStatements.AlgebraicWitnessReturned
import Paper2.HeightTwo
import Paper2.HeightOne.TensorPrimeTools
import Paper2.Tractable.Conformal

/-! Exact structural exceptions of source Theorem 2.15. Both nonzero endpoint
values and even support are used to exclude all extra clauses of the full
criterion. No tensor-primality hypothesis is imposed on the final table. -/
namespace Paper2.SourceFaithful.SourceStatements.EightVertexBoundary
open Paper2.Tractable
open AlgebraicWitness (Class Member)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def Exception (q : Signature AlgebraicComplex 4) : Prop :=
  ∃ C : Class, ∃ U : InvertibleKernel,
    Member C (kernelSignature (Kernel.pullback Signature.disequality U.matrix)) ∧
    Member C (U.symm.action q)

private def pullFactor {m n : ℕ} (r : Fin m → Fin n) : ProductFactor m → ProductFactor n
  | .unary i u h => .unary (r i) u h
  | .equality i j => .equality (r i) (r j)
  | .disequality i j => .disequality (r i) (r j)

private theorem product_pullback {m n : ℕ} {f : Signature AlgebraicComplex m}
    (hf : Product f) (r : Fin m → Fin n) : Product (fun x => f (fun j => x (r j))) := by
  rcases hf with rfl | ⟨c,hc,fs,rfl⟩
  · exact product_zero n
  · refine Or.inr ⟨c,hc,fs.map (pullFactor r),?_⟩
    funext x
    simp only [productFormula,List.map_map]
    congr 2
    apply List.map_congr_left
    intro t _
    cases t <;> rfl

private theorem product_tensor {m n : ℕ} {f : Signature AlgebraicComplex m}
    {g : Signature AlgebraicComplex n} (hf : Product f) (hg : Product g) :
    Product (Signature.tensor f g) := by
  exact (product_pullback hf (Fin.castAdd n)).mul
    (product_pullback hg (Fin.natAdd m))

private theorem weighted_product (q : Signature AlgebraicComplex 2)
    (h : HeightTwo.WeightedEquality q) : Product q := by
  have hp := (product_unary (0 : Fin 2) (fun b => q (fun _ => b))).mul
    (product_equality (0 : Fin 2) 1)
  convert hp using 1
  funext x
  have he : x = ![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [he]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [Signature.equality,h.1,h.2.1]
  all_goals congr 1; funext i; fin_cases i <;> rfl

private theorem product_exception {q : Signature AlgebraicComplex 4} (h : Product q) :
    Exception q := by
  refine ⟨.product,InvertibleKernel.identity,?_,?_⟩
  · change Product (kernelSignature (Kernel.pullback Signature.disequality Signature.equality))
    simp only [Kernel.pullback,Kernel.transpose_equality,Kernel.equality_mul,
      Kernel.mul_equality]
    change Product (fun x => Signature.disequality (x 0) (x 1))
    exact product_disequality (0 : Fin 2) 1
  · change Product (InvertibleKernel.identity.symm.action q)
    simpa only [InvertibleKernel.identity_symm,InvertibleKernel.identity_action] using h

/-- In a unary/binary decomposition of an even table with both endpoints
nonzero, every block is binary. A unary block would make a weight-one word live. -/
theorem arityTwo_blocks_binary {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (hs : ∀ i, D.arity i = 1 ∨ D.arity i = 2)
    (heven : HeightTwo.EvenSupport D.value)
    (h0 : D.value (fun _ => false) ≠ 0) (h1 : D.value (fun _ => true) ≠ 0) :
    ∀ i, D.arity i = 2 := by
  classical
  have hf0 : ∀ i, D.factor i (fun _ => false) ≠ 0 := by
    intro i hz
    have hp : (∏ j, D.factor j (fun _ => false)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact h0 (by simpa [TensorDecomposition.value] using congrArg (fun v => (D.scale : AlgebraicComplex) * v) hp)
  have hf1 : ∀ i, D.factor i (fun _ => true) ≠ 0 := by
    intro i hz
    have hp : (∏ j, D.factor j (fun _ => true)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hz
    exact h1 (by simpa [TensorDecomposition.value] using congrArg (fun v => (D.scale : AlgebraicComplex) * v) hp)
  intro i
  rcases hs i with hi | hi
  · let j : Fin (D.arity i) := ⟨0,by omega⟩
    let x : Fin n → Bool := Function.update (fun _ => false) (D.ports ⟨i,j⟩) true
    have hw : weight x = 1 := by
      simp [x,weight,Function.update_apply]
    have hl : D.value x ≠ 0 := by
      apply mul_ne_zero (Units.ne_zero D.scale)
      apply Finset.prod_ne_zero_iff.mpr
      intro k _
      by_cases hk : k = i
      · subst k
        have hx : (fun t => x (D.ports ⟨i,t⟩)) = fun _ => true := by
          funext t
          have ht : t = j := Fin.ext (by have := t.isLt; dsimp [j]; omega)
          subst t
          simp [x]
        rw [hx]
        exact hf1 i
      · have hx : (fun t => x (D.ports ⟨k,t⟩)) = fun _ => false := by
          funext t
          have hp : D.ports ⟨k,t⟩ ≠ D.ports ⟨i,j⟩ := by
            intro hp
            exact hk (congrArg Sigma.fst (D.ports.injective hp))
          simp [x,hp]
        rw [hx]
        exact hf0 k
    have hh := heven x hl
    rw [hw] at hh
    norm_num at hh
  · exact hi

private theorem prime_not_small {q : Signature AlgebraicComplex 4}
    (hp : TensorPrime q) (heven : HeightTwo.EvenSupport q)
    (h0 : q (fun _ => false) ≠ 0) (h1 : q (fun _ => true) ≠ 0) :
    ¬SourceTensorClosure (fun n _ => n = 1 ∨ n = 2) q := by
  rintro (hz | ⟨D,hD,hd⟩)
  · exact hp.1 hz
  · have ht := arityTwo_blocks_binary D hD (hd.symm ▸ heven)
      (hd.symm ▸ h0) (hd.symm ▸ h1)
    exact HeightOne.binary_decomposition_not_tensorPrime D ht (by decide) (hd.symm ▸ hp)

private def orientedK (b : Bool) : InvertibleKernel :=
  if b then sourceKBasis.comp bitFlipBasis else sourceKBasis

private theorem inverse_matching (b : Bool) (n : ℕ) (f : Signature AlgebraicComplex n)
    (h : matchingImage b n f) : Signature.OneHot ((orientedK b).symm.action f) := by
  obtain ⟨g,hg,hf⟩ := h
  have he : (orientedK b).action g = f := by
    cases b <;> exact hf
  rw [←he,InvertibleKernel.symm_action_action]
  exact hg

private theorem not_matching {q : Signature AlgebraicComplex 4}
    (heven : HeightTwo.EvenSupport q) (h0 : q (fun _ => false) ≠ 0)
    (h1 : q (fun _ => true) ≠ 0) :
    ¬MatchingAlternative (familyAction sourceKBasis {⟨4,q⟩}) := by
  have hmem : (⟨4,sourceKBasis.action q⟩ : AnySignature AlgebraicComplex) ∈
      familyAction sourceKBasis {⟨4,q⟩} := ⟨⟨4,q⟩,Set.mem_singleton _,rfl⟩
  have hf : q ≠ 0 := fun hz => h0 (congrFun hz _)
  have live (b : Bool)
      (h : SourceTensorClosure (matchingImage b) (sourceKBasis.action q)) :
      ∀ x, q x ≠ 0 := by
    rcases h with hz | ht
    · exact (hf ((Conformal.action_eq_zero_iff _ _).mp hz)).elim
    · have hc := ht.map_action (orientedK b).inverse (inverse_matching b)
      change Signature.TensorClosure (fun _ g => Signature.OneHot g)
        ((orientedK b).symm.action (sourceKBasis.action q)) at hc
      cases b with
      | false =>
        simp only [orientedK,Bool.false_eq_true,ite_false,InvertibleKernel.symm_action_action] at hc
        exact Signature.tensorClosure_oneHot_full_support hc h0 h1
      | true =>
        simp only [orientedK,ite_true,InvertibleKernel.comp_symm,InvertibleKernel.comp_action,
          InvertibleKernel.symm_action_action,bitFlipBasis_symm] at hc
        have hc0 : bitFlipBasis.action q (fun _ => false) ≠ 0 := by
          simpa only [bitFlipBasis_action,Bool.not_false] using h1
        have hc1 : bitFlipBasis.action q (fun _ => true) ≠ 0 := by
          simpa only [bitFlipBasis_action,Bool.not_true] using h0
        have hl := Signature.tensorClosure_oneHot_full_support hc hc0 hc1
        intro x
        simpa only [bitFlipBasis_action,Bool.not_not] using hl (fun i => !(x i))
  intro h
  have hl : ∀ x, q x ≠ 0 := by
    rcases h with h | h
    · exact live false (h _ hmem)
    · exact live true (h _ hmem)
  have hh := heven ![true,false,false,false] (hl _)
  have hw : weight ![true,false,false,false] = 1 := by decide
  rw [hw] at hh
  norm_num at hh

private theorem not_one_sided {q : Signature AlgebraicComplex 4}
    (h0 : q (fun _ => false) ≠ 0) (h1 : q (fun _ => true) ≠ 0) :
    ¬OneSidedAlternative (familyAction sourceKBasis {⟨4,q⟩}) := by
  rintro ⟨h,_⟩
  rw [Conformal.kCoordinates_familyAction] at h
  rcases h with h | h
  · have hh := h ⟨4,q⟩ (Set.mem_singleton _) (fun _ => false) h0
    norm_num [charge,weight] at hh
  · have hh := h ⟨4,q⟩ (Set.mem_singleton _) (fun _ => true) h1
    norm_num [charge,weight] at hh

private theorem not_single_weight {q : Signature AlgebraicComplex 4}
    (h0 : q (fun _ => false) ≠ 0) (h1 : q (fun _ => true) ≠ 0) :
    ¬SingleWeightAlternative (familyAction sourceKBasis {⟨4,q⟩}) := by
  intro h
  unfold SingleWeightAlternative at h
  rw [Conformal.kCoordinates_familyAction] at h
  obtain ⟨d,hd⟩ := h.1 ⟨4,q⟩ (Set.mem_singleton _)
  have hz : weight (fun _ : Fin 4 => false) = d := by
    by_contra hz
    exact h0 (hd _ hz)
  have ho : weight (fun _ : Fin 4 => true) = d := by
    by_contra ho
    exact h1 (hd _ ho)
  norm_num [weight] at hz ho
  omega

private theorem exception_of_common (C : Class) (q : Signature AlgebraicComplex 4)
    (h : CommonTransformable {f | Member C f.2} (familyAction sourceKBasis {⟨4,q⟩})) :
    Exception q := by
  obtain ⟨_,U,hE,hG⟩ := (commonTransformable_iff_commonKPresentation _ _).mp h
  refine ⟨C,U,hE,?_⟩
  have hm : (⟨4,sourceKBasis.action q⟩ : AnySignature AlgebraicComplex) ∈
      familyAction sourceKBasis {⟨4,q⟩} := ⟨⟨4,q⟩,Set.mem_singleton _,rfl⟩
  have hg := hG _ hm
  change Member C (U.symm.action (sourceKBasis.symm.action (sourceKBasis.action q))) at hg
  simpa only [InvertibleKernel.symm_action_action] using hg

/-- For the broad even quaternary boundary, the full seven alternatives
collapse to precisely the three common A/P/L exceptions with the native edge. -/
theorem exception_of_tract (q : Signature AlgebraicComplex 4)
    (heven : HeightTwo.EvenSupport q) (h0 : q (fun _ => false) ≠ 0)
    (h1 : q (fun _ => true) ≠ 0)
    (ht : Tract (familyAction sourceKBasis {⟨4,q⟩})) : Exception q := by
  rcases HeightTwo.prime_or_weightedEquality_product q heven h0 h1 with hp | ⟨A,B,e,he,hA,hB⟩
  · have hpre : Preprocessed (familyAction sourceKBasis {⟨4,q⟩}) :=
      Conformal.preprocessed_familyAction _ (by
        intro f hf
        have he : f = ⟨4,q⟩ := Set.mem_singleton_iff.mp hf
        subst f
        exact ⟨by change 0 < 4; decide,fun hz => h0 (congrFun hz _)⟩)
    rw [Tract,preprocess_eq_self hpre] at ht
    rcases ht.2 with h | h | h | h | h | h | h
    · exact (not_one_sided h0 h1 h).elim
    · exact (not_single_weight h0 h1 h).elim
    · have hs := Conformal.arityTwo_map sourceKBasis.symm h
      rw [Conformal.familyAction_symm_action] at hs
      exact (prime_not_small hp heven h0 h1 (hs _ (Set.mem_singleton _))).elim
    · exact (not_matching heven h0 h1 h).elim
    · exact exception_of_common .affine q h
    · exact exception_of_common .product q h
    · exact exception_of_common .localAffine q h
  · apply product_exception
    rw [←he]
    exact product_pullback (product_tensor (weighted_product A hA) (weighted_product B hB)) e

/-- The same common edge-and-table witness supplies one of the three
transformable clauses. This direction does not require endpoint conditions. -/
theorem tract_of_exception (q : Signature AlgebraicComplex 4) (h : Exception q) :
    Tract (familyAction sourceKBasis {⟨4,q⟩}) := by
  obtain ⟨C,U,hE,hq⟩ := h
  have hfin : (familyAction sourceKBasis {⟨4,q⟩}).Finite :=
    (Conformal.familyAction_finite_iff _ _).mpr (Set.finite_singleton _)
  have hp : CommonKPresentation {f | Member C f.2}
      (familyAction sourceKBasis {⟨4,q⟩}) := by
    refine ⟨hfin,U,hE,?_⟩
    rintro f ⟨g,hg,rfl⟩
    have hgq : g = ⟨4,q⟩ := Set.mem_singleton_iff.mp hg
    subst g
    simpa only [Set.mem_ofPred_eq,InvertibleKernel.symm_action_action] using hq
  have hc := (commonTransformable_iff_commonKPresentation _ _).mpr hp
  have hpfin : (preprocess (familyAction sourceKBasis {⟨4,q⟩})).Finite :=
    hfin.subset (fun _ hf => hf.1)
  have hcp : CommonTransformable {f | Member C f.2}
      (preprocess (familyAction sourceKBasis {⟨4,q⟩})) :=
    hc.mono_family (fun _ hf => hf.1)
  refine ⟨hpfin,?_⟩
  cases C with
  | affine =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcp))))
  | product =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcp)))))
  | localAffine =>
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hcp)))))

/-- Exact source 2.15 exception predicate for the broad even boundary. -/
theorem tract_iff_exception (q : Signature AlgebraicComplex 4)
    (heven : HeightTwo.EvenSupport q) (h0 : q (fun _ => false) ≠ 0)
    (h1 : q (fun _ => true) ≠ 0) :
    Tract (familyAction sourceKBasis {⟨4,q⟩}) ↔ Exception q :=
  ⟨exception_of_tract q heven h0 h1,tract_of_exception q⟩

end
end Paper2.SourceFaithful.SourceStatements.EightVertexBoundary

