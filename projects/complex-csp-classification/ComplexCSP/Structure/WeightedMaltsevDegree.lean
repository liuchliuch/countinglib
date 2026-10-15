import ComplexCSP.Structure.WeightedMaltsevContextCompiler
import ComplexCSP.Structure.DegreeStructuralCollapse
import ComplexCSP.Recognition.DegreeConditionsTransport

/-! # Exact weighted evaluation on the genuine degree-divisible promise

Only the degree-generated family is used at every marginal. Original constraint
supports are preserved by the same fixed Mal'tsev operation because δ repeated
copies realize their positive powers with identical support when δ>0.
-/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness ComplexityWitnessEncoding
open scoped BigOperators

/-- δ copies of one original constraint have every occurrence degree divisible
by δ, and compute the actual δ-th power, including all zero entries. -/
theorem language_value_power_degreeGenerated {D K ι : Type} [Fintype D] [CommSemiring K]
    (L : Language D K ι) (i : ι) (δ : ℕ) :
    DegreeGenerated L δ (fun a => L.value i a ^ δ) := by
  classical
  let I : Instance L (Fin (L.arity i)) (Fin 0) := ⟨List.replicate δ ⟨i,Sum.inl⟩⟩
  refine ⟨⟨0,I⟩,?_,?_⟩
  · intro v
    change δ ∣ I.occurrenceDegree v
    simp only [I,Instance.occurrenceDegree,Instance.occurrences,List.flatMap_replicate,
      List.count_flatten,List.map_replicate,List.sum_replicate]
    exact dvd_mul_right δ _
  · funext a
    simp [Presentation.table,I,Instance.partition,Instance.eval,Constraint.eval,Function.comp_def]

variable {K : Type} [Field K] [DecidableEq K] {d s : ℕ}

omit [DecidableEq K] in
theorem degree_generated_marginal {L : Language (Fin d) K (Fin s)} {δ n : ℕ}
    (G : (Fin (n + 1) → Fin d) → K) (hG : DegreeGenerated L δ G) :
    DegreeGenerated L δ (marginal G) := by
  have hrename := hG.diagonal_minor (splitLastScope n)
  have hsum := hrename.marginal_finite (H:=Fin 1)
  convert hsum using 1
  funext x
  simp only [marginal,splitLast_assignment]
  exact ((Equiv.funUnique (Fin 1) (Fin d)).sum_comp (fun a => G (Fin.snoc x a))).symm

omit [DecidableEq K] in
theorem embedded_degree_support_preserves (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {δ : ℕ} {m : Operation (Fin d)} (hs : CommonPolymorphism (degreeGeneratedSupports (L.mapValues σ) δ) m)
    {n : ℕ} (G : (Fin n → Fin d) → K) (hG : DegreeGenerated L δ G) :
    Preserves m {x | G x ≠ 0} := by
  have hG' := hG.mapValues σ
  let R : Relation (Fin d) := ⟨n,{x | σ (G x) ≠ 0}⟩
  have h := hs R ⟨_,hG',rfl⟩
  simpa only [R,map_ne_zero] using h

omit [DecidableEq K] in
/-- Positive powers transfer the common degree-family operation to every
original constraint support without asserting unrestricted BO. -/
theorem degree_common_preserves_tables (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {δ : ℕ} (hδ : 0<δ) {m : Operation (Fin d)}
    (hs : CommonPolymorphism (degreeGeneratedSupports (L.mapValues σ) δ) m) :
    ∀ i,Preserves m {x | L.value i x ≠ 0} := by
  intro i
  have h := embedded_degree_support_preserves L σ hs (fun x => L.value i x ^ δ)
    (language_value_power_degreeGenerated L i δ)
  have he : {x | L.value i x ^ δ ≠ 0}={x | L.value i x ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq,ne_eq,pow_eq_zero_iff (Nat.ne_of_gt hδ)]
  rwa [he] at h

theorem embedded_degree_row_hypotheses (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {δ : ℕ} {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hrow : ∀ (n : ℕ), 0<n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      DegreeGenerated (L.mapValues σ) δ G → Preserves m (RowTypes.omegaRelation G).tuples)
    {n : ℕ} (G : (Fin (n+1) → Fin d) → K) (hG : DegreeGenerated L δ G) :
    Preserves m (rowSupport G) ∧ AllTypesPartition (rowSupport G) (fun x => tableLabel G (view x)) ∧
      ∀ a,Preserves m (rowFiber G a) := by
  apply omega_supplies_layer_hypotheses G σ hm
  cases n with
  | zero => exact omega_zero_preserved _ m
  | succ n => exact hrow (n+1) (Nat.succ_pos _) _ (hG.mapValues σ)

/-- Every recursive marginal carries its actual degree witness. The algorithm
is the identical concrete evaluator used in the ordinary theorem. -/
theorem eliminate_correct_degree (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {δ : ℕ} {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (degreeGeneratedSupports (L.mapValues σ) δ) m)
    (hrow : ∀ (n : ℕ), 0<n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      DegreeGenerated (L.mapValues σ) δ G → Preserves m (RowTypes.omegaRelation G).tuples)
    (defaultValue : Fin d) (n : ℕ) (G : (Fin n → Fin d) → K)
    (hG : DegreeGenerated L δ G) (W : StoredCode d n) (hW : Correct W.toCode {x | G x ≠ 0})
    (evaluate : Tuple (Fin d) n → K) (he : ∀x,evaluate x=G (view x)) :
    eliminate m defaultValue evaluate W=∑x,G x := by
  induction n with
  | zero =>
    change evaluate (Vector.ofFn Fin.elim0)=_
    rw [he]
    simp only [view_ofFn,Fintype.sum_unique]
    exact congrArg G (Subsingleton.elim _ _)
  | succ n ih =>
    obtain ⟨hR,hTP,hclasses⟩ := embedded_degree_row_hypotheses L σ hm hrow G hG
    let layer := buildLayer m W.toCode evaluate defaultValue
    have hv : ValidLayer G layer := buildLayer_correct hm G hW hR hTP hclasses evaluate he defaultValue
    have hM := degree_generated_marginal G hG
    have hpres := embedded_degree_support_preserves L σ hs (marginal G) hM
    have hnext := marginalSupportCode_correct hm G layer hv hclasses hpres
    have hresult := ih (marginal G) hM (marginalSupportCode m layer) hnext
      (evaluateLayer m layer evaluate) (evaluateLayer_correct hm G layer hv hclasses evaluate he)
    exact hresult.trans (sum_marginal G)

omit [DecidableEq K] in
/-- Exposing all raw variables keeps literal occurrence degrees. -/
theorem raw_assignment_degreeGenerated (L : Language (Fin d) K (Fin s))
    {δ : ℕ} (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (hdegree : (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ) :
    DegreeGenerated L δ (ComplexityCSPCode.eval L g) := by
  let I : Instance L (Fin g.vertices) (Fin 0) :=
    (ComplexityCSPCode.toInstance L g hg).mapVariables Sum.swap
  refine ⟨⟨0,I⟩,hdegree.mapVariables Sum.swap,?_⟩
  funext x
  have he : I.eval x Fin.elim0=ComplexityCSPCode.eval L g x := by
    calc
      _ = (ComplexityCSPCode.toInstance L g hg).eval Fin.elim0 x := by
        simp [I,Instance.eval,Instance.mapVariables,Constraint.eval,Constraint.rename,Function.comp_def,
          ComplexityCSPCode.toInstance]
      _ = _ := ComplexityCSPCode.eval_toInstance L g hg x
  rw [Presentation.table, Instance.partition, Fintype.sum_unique]
  exact (congrArg (I.eval x)
    (Subsingleton.elim (default : Fin 0 → Fin d) Fin.elim0)).trans he

/-- One operation computes every degree-valid partition, with no assumption
that the original language satisfies ordinary JointBO. -/
theorem degreeJointBO_exact_evaluator [Nonempty (Fin d)] (L : Language (Fin d) K (Fin s))
    (σ : K →+* ℂ) {δ : ℕ} (hδ : 0<δ)
    (hAlg : ∀i a,IsAlgebraic ℚ ((L.mapValues σ).value i a)) (hBO : DegreeJointBO (L.mapValues σ) δ)
    (defaultValue : Fin d) :
    ∃m : Operation (Fin d),IsMaltsev m ∧
      ∀(g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g),
        (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ →
        evaluateRaw L m defaultValue g hg=ComplexityCSPCode.partition L g := by
  obtain ⟨m,hm,hs,hrow⟩ := DegreeStructuralCollapse.common_support_and_row_maltsev (L.mapValues σ) δ hAlg hBO
  refine ⟨m,hm,?_⟩
  intro g hg hdegree
  have htables := degree_common_preserves_tables L σ hδ hs
  exact eliminate_correct_degree L σ hm hs hrow defaultValue g.vertices (ComplexityCSPCode.eval L g)
    (raw_assignment_degreeGenerated L g hg hdegree) (rawSupportWitness L m defaultValue g hg)
    (rawSupportWitness_correct L hm htables defaultValue g hg) _ (fun _ => rfl)

omit [DecidableEq K] in
/-- Each literal prefix marginal is generated by the original finite language. -/
theorem degree_generated_prefixMarginal (L : Language (Fin d) K (Fin s))
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    {δ : ℕ} (hdegree : (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ)
    (k : ℕ) (hk : k ≤ g.vertices) :
    DegreeGenerated L δ (ComplexityCSPMarginalBounds.marginal L g hk) := by
  have aux : ∀ (fuel k : ℕ) (he : k + fuel = g.vertices),
      DegreeGenerated L δ (ComplexityCSPMarginalBounds.marginal L g (by omega : k ≤ g.vertices)) := by
    intro fuel
    induction fuel with
    | zero =>
      intro k he
      have hk' : k = g.vertices := by omega
      subst k
      have heq : ComplexityCSPMarginalBounds.marginal L g (by omega) = ComplexityCSPCode.eval L g := by
        funext x
        exact ComplexityCSPMarginalBounds.marginal_full L g x
      rw [heq]
      exact raw_assignment_degreeGenerated L g hg hdegree
    | succ fuel ih =>
      intro k he
      have hnext := ih (k+1) (by omega)
      have hmarg := degree_generated_marginal _ hnext
      have heq : marginal (ComplexityCSPMarginalBounds.marginal L g (by omega : k+1 ≤ g.vertices)) =
          ComplexityCSPMarginalBounds.marginal L g (by omega : k ≤ g.vertices) := by
        funext x
        exact (ComplexityCSPMarginalBounds.marginal_succ L g _ _ x).symm
      rwa [heq] at hmarg
  exact aux (g.vertices-k) k (Nat.add_sub_of_le hk)


section PositiveDomain
variable [NeZero d]

/-- Every stage in the actual context recursion preserves the exact raw
ComputeF marginal invariant and the actually constructed support witness. -/
theorem compileContextLayers_correct_degree (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {δ : ℕ} {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (degreeGeneratedSupports (L.mapValues σ) δ) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      DegreeGenerated (L.mapValues σ) δ G → Preserves m (RowTypes.omegaRelation G).tuples)
    (defaultValue : Fin d) (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (hdegree : (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ)
    (n : ℕ) (hn : n ≤ g.vertices) (W : StoredCode d n)
    (hW : Correct W.toCode {x | ComplexityCSPMarginalBounds.marginal L g hn x ≠ 0})
    (layers : List (ComplexityWeightedLayers.Layer K)) (hrep : RepresentsMarginal L m g hn layers) :
    ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g []
      (compileContextLayers L m defaultValue g W layers) = ComplexityCSPCode.partition L g := by
  induction n generalizing layers with
  | zero =>
    have h := hrep (Vector.ofFn Fin.elim0)
    simpa [compileContextLayers,word,Vector.toList_ofFn,List.ofFn_zero,ComplexityCSPMarginalBounds.marginal_empty] using h
  | succ n ih =>
    let G := ComplexityCSPMarginalBounds.marginal L g hn
    have hG : DegreeGenerated L δ G := degree_generated_prefixMarginal L g hg hdegree (n+1) hn
    obtain ⟨hR,hTP,hclasses⟩ := embedded_degree_row_hypotheses L σ hm hrow G hG
    let evaluate := fun x : Tuple (Fin d) (n+1) => ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g (word x) layers
    let layer := buildLayer m W.toCode evaluate defaultValue
    have hv : ValidLayer G layer := buildLayer_correct hm G hW hR hTP hclasses evaluate hrep defaultValue
    have heq : marginal G = ComplexityCSPMarginalBounds.marginal L g (by omega : n ≤ g.vertices) := by
      funext x
      exact (ComplexityCSPMarginalBounds.marginal_succ L g _ hn x).symm
    have hpres := embedded_degree_support_preserves L σ hs (marginal G) (degree_generated_marginal G hG)
    have hnext := marginalSupportCode_correct hm G layer hv hclasses hpres
    rw [heq] at hnext
    have hr := representsMarginal_prepend L hm g (by omega) hn layers hrep layer hv hclasses
    exact ih (by omega) (marginalSupportCode m layer) hnext (encodeLayer layer::layers) hr


/-- The same immutable-context constructor is correct on the actual degree
promise. Its layer callbacks remain the concrete original-instance executor. -/
theorem degreeJointBO_context_execution [Nonempty (Fin d)] (L : Language (Fin d) K (Fin s))
    (σ : K →+* ℂ) {δ : ℕ} (hδ : 0<δ)
    (hAlg : ∀i a,IsAlgebraic ℚ ((L.mapValues σ).value i a)) (hBO : DegreeJointBO (L.mapValues σ) δ)
    (defaultValue : Fin d) :
    ∃m : Operation (Fin d),IsMaltsev m ∧
      ∀(g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g),
        (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ →
        ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g []
          (compileRawContextLayers L m defaultValue g hg)=ComplexityCSPCode.partition L g := by
  obtain ⟨m,hm,hs,hrow⟩ := DegreeStructuralCollapse.common_support_and_row_maltsev (L.mapValues σ) δ hAlg hBO
  refine ⟨m,hm,?_⟩
  intro g hg hdegree
  have htables := degree_common_preserves_tables L σ hδ hs
  have hW := rawSupportWitness_correct L hm htables defaultValue g hg
  have heq : ComplexityCSPMarginalBounds.marginal L g le_rfl=ComplexityCSPCode.eval L g := by
    funext x
    exact ComplexityCSPMarginalBounds.marginal_full L g x
  apply compileContextLayers_correct_degree L σ hm hs hrow defaultValue g hg hdegree g.vertices le_rfl
    (rawSupportWitness L m defaultValue g hg)
  · rwa [heq]
  · exact representsMarginal_empty L m g hg

end PositiveDomain

end ComplexCSP.WeightedMaltsev
