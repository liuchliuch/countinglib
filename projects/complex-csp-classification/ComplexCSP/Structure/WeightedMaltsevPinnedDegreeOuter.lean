import ComplexCSP.Structure.WeightedMaltsevPinnedOuter
import ComplexCSP.Structure.WeightedMaltsevPinnedDegree

/-! # Reached-context correctness and caps under positive DegreeJointBO

The raw and typed pinned constructors are exactly the ordinary implementations.
Only the promise-specific semantic proofs differ: original and every prefix
marginal carry genuine δ-divisible witnesses, without ordinary JointBO.
-/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityCSPMarginalRowBounds ComplexityCSPMarginalCacheBounds ComplexityWitnessSizeBounds
open ComplexityEncodingBounds
open PlanarHom PlanarHom.Complexity PlanarHom.MachineComposition
variable {K : Type} [Field K] [DecidableEq K] {d s : ℕ} [NeZero d]

theorem pinnedOuterStep_correct_degree (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {δ : ℕ} {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (degreeGeneratedSupports (L.mapValues σ) δ) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      DegreeGenerated (L.mapValues σ) δ G → Preserves m (RowTypes.omegaRelation G).tuples)
    (defaultValue : Fin d) (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (hdegree : (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ)
    {n : ℕ} (hn1 : n+1 ≤ g.vertices) (W : StoredCode d (n+1))
    (hW : Correct W.toCode {x | ComplexityCSPMarginalBounds.marginal L g hn1 x ≠ 0})
    (layers : List (ComplexityWeightedLayers.Layer K)) (hrep : RepresentsMarginal L m g hn1 layers) :
    Correct (pinnedOuterStep L m defaultValue g W layers).1.toCode
      {x | ComplexityCSPMarginalBounds.marginal L g (by omega : n ≤ g.vertices) x ≠ 0} ∧
    RepresentsMarginal L m g (by omega : n ≤ g.vertices)
      (pinnedOuterStep L m defaultValue g W layers).2 := by
  let G := ComplexityCSPMarginalBounds.marginal L g hn1
  have hG : DegreeGenerated L δ G := degree_generated_prefixMarginal L g hg hdegree (n+1) hn1
  have hEq := embedded_degree_row_equivalence L σ hrow G hG
  obtain ⟨_,_,hclasses⟩ := embedded_degree_row_hypotheses L σ hm hrow G hG
  let evaluate := fun x : Tuple (Fin d) (n+1) => ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g (word x) layers
  let layer := buildPinnedLayer m W.toCode evaluate defaultValue
  have hv : ValidLayer G layer := buildPinnedLayer_correct hm G hW hEq evaluate hrep defaultValue
  have heq : marginal G = ComplexityCSPMarginalBounds.marginal L g (by omega : n ≤ g.vertices) := by
    funext x
    exact (ComplexityCSPMarginalBounds.marginal_succ L g _ hn1 x).symm
  have hpres := embedded_degree_support_preserves L σ hs (marginal G) (degree_generated_marginal G hG)
  have hnext := marginalSupportCode_correct hm G layer hv hclasses hpres
  rw [heq] at hnext
  exact ⟨hnext,representsMarginal_prepend L hm g (by omega) hn1 layers hrep layer hv hclasses⟩


theorem pinnedOuterReach_correct_degree (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {δ : ℕ} (hδ : 0 < δ) {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (degreeGeneratedSupports (L.mapValues σ) δ) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      DegreeGenerated (L.mapValues σ) δ G → Preserves m (RowTypes.omegaRelation G).tuples)
    (defaultValue : Fin d) (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (hdegree : (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ)
    {n : ℕ} {W : StoredCode d n} {layers : List (ComplexityWeightedLayers.Layer K)}
    (hr : PinnedOuterReach L m defaultValue g hg W layers) :
    ∃ hn : n ≤ g.vertices,
      Correct W.toCode {x | ComplexityCSPMarginalBounds.marginal L g hn x ≠ 0} ∧
      RepresentsMarginal L m g hn layers := by
  induction hr with
  | start =>
    have htables := degree_common_preserves_tables L σ hδ hs
    refine ⟨le_rfl,?_,representsMarginal_empty L m g hg⟩
    have hW := rawSupportWitness_correct L hm htables defaultValue g hg
    have heq : ComplexityCSPMarginalBounds.marginal L g le_rfl = ComplexityCSPCode.eval L g := by
      funext x; exact ComplexityCSPMarginalBounds.marginal_full L g x
    rwa [heq]
  | @next n W layers hr ih =>
    obtain ⟨hn,hW,hrep⟩ := ih
    exact ⟨by omega,pinnedOuterStep_correct_degree L σ hm hs hrow defaultValue g hg hdegree hn W hW layers hrep⟩


section BitBounds
variable [Algebra ℚ K] {dimension : ℕ}

theorem exists_pinnedOuter_layer_bits_degree (L : Language (Fin d) K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ)
    {δ : ℕ} (hδ : 0 < δ) {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (degreeGeneratedSupports (L.mapValues σ) δ) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      DegreeGenerated (L.mapValues σ) δ G → Preserves m (RowTypes.omegaRelation G).tuples)
    (hBO : DegreeJointBO (L.mapValues σ) δ) (defaultValue : Fin d) : ∃ p : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (_hdegree : (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ)
      {n : ℕ} {W : StoredCode d n} {layers : List (ComplexityWeightedLayers.Layer K)},
      PinnedOuterReach L m defaultValue g hg W layers →
      ∀ layer ∈ layers, ((ComplexityWeightedLayers.layerCode basis).encode layer).length ≤
        p.eval (ComplexityCSPCode.encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_buildPinnedLayer_output_bound L basis
  refine ⟨p,?_⟩
  intro g hg hdegree n W layers hr
  induction hr with
  | start => simp
  | @next n W layers hr ih =>
    obtain ⟨hn,hW,hrep⟩ := pinnedOuterReach_correct_degree L σ hδ hm hs hrow defaultValue g hg hdegree hr
    let G := ComplexityCSPMarginalBounds.marginal L g hn
    have hG : DegreeGenerated L δ G := degree_generated_prefixMarginal L g hg hdegree (n+1) hn
    have hEq := embedded_degree_row_equivalence L σ hrow G hG
    have hb : BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows G x a)) :=
      (DegreeJointBO.original (L.mapValues σ) δ hBO) n (fun x => σ (G x)) (hG.mapValues σ)
    intro layer he
    change layer ∈ _ :: layers at he
    rcases List.mem_cons.mp he with rfl | he
    · exact hp g hg n hn m hm W.toCode hW hEq _ hrep defaultValue σ hb
    · exact ih layer he


theorem exists_pinnedOuter_context_bound_degree (L : Language (Fin d) K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ)
    {δ : ℕ} (hδ : 0 < δ) {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (degreeGeneratedSupports (L.mapValues σ) δ) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      DegreeGenerated (L.mapValues σ) δ G → Preserves m (RowTypes.omegaRelation G).tuples)
    (hBO : DegreeJointBO (L.mapValues σ) δ) (defaultValue : Fin d) : ∃ p : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (_hdegree : (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ)
      {n : ℕ} {W : StoredCode d n} {layers : List (ComplexityWeightedLayers.Layer K)},
      PinnedOuterReach L m defaultValue g hg W layers →
      ((ComplexityTypeStackConcrete.contextCode basis).encode
        (ComplexityTypeStackConcrete.storedContext (g,layers) W)).length ≤
          p.eval (ComplexityCSPCode.encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_pinnedOuter_layer_bits_degree L basis σ hδ hm hs hrow hBO defaultValue
  refine ⟨outerContextPolynomial d p,?_⟩
  intro g hg hdegree n W layers hr
  let N := (ComplexityCSPCode.encoding.encode g).length
  have hN : g.vertices ≤ N := (Nat.le_add_right _ _).trans (ComplexityCSPCode.size_le_encoding_length g)
  have hlen := hr.length_eq
  have hn : n ≤ N := by omega
  have hlayers : layers.length ≤ N := by omega
  have hb := encoded_list_le (ComplexityWeightedLayers.layerCode basis) layers (p.eval N)
    (hp g hg hdegree hr)
  have hb' : (((ComplexityWeightedLayers.layerCode basis).list).encode layers).length ≤
      (6*p.eval N+3)*N+1 := hb.trans (by gcongr)
  have hc := storedContext_code_bound basis g W layers _ hb'
  have hw := natPolynomial_monotone (storedPolynomial d) hn
  simp only [outerContextPolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_ofNat,Polynomial.eval_one]
  change _ ≤ 6*N + 2*((6*p.eval N+3)*N+1) + (storedPolynomial d).eval N + 4
  dsimp only [N] at hc hw hn ⊢
  omega

end BitBounds
end ComplexCSP.WeightedMaltsev
