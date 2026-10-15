import ComplexCSP.Structure.WeightedMaltsevPinnedLayer
import ComplexCSP.Structure.WeightedMaltsevDegree

/-! # The same pinned evaluator on the genuine positive-degree promise

No unrestricted JointBO premise is used. Every marginal retains its actual
degree-generated witness, and δ>0 transfers the common operation to original
constraint supports using δ copies and equality of positive-power supports.
-/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness ComplexityWitnessEncoding
variable {K : Type} [Field K] [DecidableEq K] {d s n : ℕ}

theorem embedded_degree_row_equivalence (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {δ : ℕ} {m : Operation (Fin d)}
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      DegreeGenerated (L.mapValues σ) δ G → Preserves m (RowTypes.omegaRelation G).tuples)
    (G : (Fin (n+1) → Fin d) → K) (hG : DegreeGenerated L δ G) :
    PreservesRowEquivalence m (rowFiber G) := by
  apply row_equivalence_of_omega G σ
  cases n with
  | zero => exact omega_zero_preserved _ m
  | succ n => exact hrow (n+1) (Nat.succ_pos _) _ (hG.mapValues σ)


section PositiveDomain
variable [NeZero d]

theorem compilePinnedContextLayers_correct_degree (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
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
      (compilePinnedContextLayers L m defaultValue g W layers) = ComplexityCSPCode.partition L g := by
  induction n generalizing layers with
  | zero =>
    have h := hrep (Vector.ofFn Fin.elim0)
    simpa [compilePinnedContextLayers,word,Vector.toList_ofFn,List.ofFn_zero,ComplexityCSPMarginalBounds.marginal_empty] using h
  | succ n ih =>
    let G := ComplexityCSPMarginalBounds.marginal L g hn
    have hG : DegreeGenerated L δ G := degree_generated_prefixMarginal L g hg hdegree (n+1) hn
    have hEq := embedded_degree_row_equivalence L σ hrow G hG
    obtain ⟨hR,hTP,hclasses⟩ := embedded_degree_row_hypotheses L σ hm hrow G hG
    let evaluate := fun x : Tuple (Fin d) (n+1) => ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g (word x) layers
    let layer := buildPinnedLayer m W.toCode evaluate defaultValue
    have hv : ValidLayer G layer := buildPinnedLayer_correct hm G hW hEq evaluate hrep defaultValue
    have heq : marginal G = ComplexityCSPMarginalBounds.marginal L g (by omega : n ≤ g.vertices) := by
      funext x
      exact (ComplexityCSPMarginalBounds.marginal_succ L g _ hn x).symm
    have hpres := embedded_degree_support_preserves L σ hs (marginal G) (degree_generated_marginal G hG)
    have hnext := marginalSupportCode_correct hm G layer hv hclasses hpres
    rw [heq] at hnext
    have hr := representsMarginal_prepend L hm g (by omega) hn layers hrep layer hv hclasses
    exact ih (by omega) (marginalSupportCode m layer) hnext (encodeLayer layer::layers) hr


theorem degreeJointBO_pinned_context_execution [Nonempty (Fin d)] (L : Language (Fin d) K (Fin s))
    (σ : K →+* ℂ) {δ : ℕ} (hδ : 0<δ)
    (hAlg : ∀i a,IsAlgebraic ℚ ((L.mapValues σ).value i a)) (hBO : DegreeJointBO (L.mapValues σ) δ)
    (defaultValue : Fin d) :
    ∃m : Operation (Fin d),IsMaltsev m ∧
      ∀(g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g),
        (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ →
        ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g []
          (compileRawPinnedContextLayers L m defaultValue g hg)=ComplexityCSPCode.partition L g := by
  obtain ⟨m,hm,hs,hrow⟩ := DegreeStructuralCollapse.common_support_and_row_maltsev (L.mapValues σ) δ hAlg hBO
  refine ⟨m,hm,?_⟩
  intro g hg hdegree
  have htables := degree_common_preserves_tables L σ hδ hs
  have hW := rawSupportWitness_correct L hm htables defaultValue g hg
  have heq : ComplexityCSPMarginalBounds.marginal L g le_rfl=ComplexityCSPCode.eval L g := by
    funext x
    exact ComplexityCSPMarginalBounds.marginal_full L g x
  apply compilePinnedContextLayers_correct_degree L σ hm hs hrow defaultValue g hg hdegree g.vertices le_rfl
    (rawSupportWitness L m defaultValue g hg)
  · rwa [heq]
  · exact representsMarginal_empty L m g hg

end PositiveDomain
end ComplexCSP.WeightedMaltsev
