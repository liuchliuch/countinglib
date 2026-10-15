import ComplexCSP.Structure.WeightedMaltsevPinnedBounds
import ComplexCSP.Complexity.TypeStackConcrete

/-! # Actual pinned outer-loop reachability and original-instance state bounds

The reachability relation follows the concrete constructor's actual data
updates. Semantic and bit-size invariants are derived for every reached context,
including zero dimension, empty support and cancellation. These bounds justify
that an independently compiled total capped outer iterator never caps a genuine
execution; they do not assume correctness or bounds of a raw constructor oracle.
-/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityCSPMarginalRowBounds ComplexityCSPMarginalCacheBounds ComplexityWitnessSizeBounds
open ComplexityEncodingBounds
open PlanarHom PlanarHom.Complexity PlanarHom.MachineComposition
variable {K : Type} [Field K] [DecidableEq K] {d s : ℕ}

/-- Exact changing data for one successor stage of the pinned constructor. -/
def pinnedOuterStep (L : Language (Fin d) K (Fin s)) (m : Operation (Fin d))
    (defaultValue : Fin d) (g : ComplexityCSPCode.Code) {n : ℕ}
    (W : StoredCode d (n+1)) (layers : List (ComplexityWeightedLayers.Layer K)) :
    StoredCode d n × List (ComplexityWeightedLayers.Layer K) :=
  let evaluate := fun x => ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g (word x) layers
  let layer := buildPinnedLayer m W.toCode evaluate defaultValue
  (marginalSupportCode m layer,encodeLayer layer::layers)

@[simp] theorem compilePinnedContextLayers_succ (L : Language (Fin d) K (Fin s))
    (m : Operation (Fin d)) (defaultValue : Fin d) (g : ComplexityCSPCode.Code) {n : ℕ}
    (W : StoredCode d (n+1)) (layers : List (ComplexityWeightedLayers.Layer K)) :
    compilePinnedContextLayers L m defaultValue g W layers =
      compilePinnedContextLayers L m defaultValue g
        (pinnedOuterStep L m defaultValue g W layers).1
        (pinnedOuterStep L m defaultValue g W layers).2 := rfl

/-- Actual finite prefixes of the outer construction, with no correctness or
space bounds built into the relation. -/
inductive PinnedOuterReach (L : Language (Fin d) K (Fin s)) (m : Operation (Fin d))
    (defaultValue : Fin d) (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) :
    {n : ℕ} → StoredCode d n → List (ComplexityWeightedLayers.Layer K) → Prop
  | start : PinnedOuterReach L m defaultValue g hg (rawSupportWitness L m defaultValue g hg) []
  | next {n : ℕ} {W : StoredCode d (n+1)} {layers} : PinnedOuterReach L m defaultValue g hg W layers →
      PinnedOuterReach L m defaultValue g hg
        (pinnedOuterStep L m defaultValue g W layers).1
        (pinnedOuterStep L m defaultValue g W layers).2

/-- One stage removes one variable and prepends exactly one materialized layer. -/
theorem PinnedOuterReach.length_eq {L : Language (Fin d) K (Fin s)} {m : Operation (Fin d)}
    {defaultValue : Fin d} {g : ComplexityCSPCode.Code} {hg : ComplexityCSPCode.Valid L g}
    {n : ℕ} {W : StoredCode d n} {layers : List (ComplexityWeightedLayers.Layer K)}
    (hr : PinnedOuterReach L m defaultValue g hg W layers) : n+layers.length = g.vertices := by
  induction hr with
  | start => simp
  | next _ ih => simpa only [pinnedOuterStep,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih

/-- Lift an actual raw one-step implementation equation to the complete typed
constructor trace. The local equation is a compiler representation contract;
this theorem does not assume an evaluator or a tractability conclusion. -/
theorem pinnedOuterReach_iterate
    (L : Language (Fin d) K (Fin s)) (m : Operation (Fin d)) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (advance : ComplexityTypeStackConcrete.Context K → ComplexityTypeStackConcrete.Context K)
    (hstep : ∀ (n : ℕ) (W : StoredCode d (n+1)) (layers : List (ComplexityWeightedLayers.Layer K)),
      PinnedOuterReach L m defaultValue g hg W layers →
      advance (ComplexityTypeStackConcrete.storedContext (g,layers) W) =
        ComplexityTypeStackConcrete.storedContext
          (g,(pinnedOuterStep L m defaultValue g W layers).2)
          (pinnedOuterStep L m defaultValue g W layers).1)
    (n : ℕ) (W : StoredCode d n) (layers : List (ComplexityWeightedLayers.Layer K))
    (hr : PinnedOuterReach L m defaultValue g hg W layers) :
    ∃ W0 : StoredCode d 0,
      advance^[n] (ComplexityTypeStackConcrete.storedContext (g,layers) W) =
        ComplexityTypeStackConcrete.storedContext
          (g,compilePinnedContextLayers L m defaultValue g W layers) W0 ∧
      PinnedOuterReach L m defaultValue g hg W0 (compilePinnedContextLayers L m defaultValue g W layers) := by
  induction n generalizing layers with
  | zero => exact ⟨W,rfl,hr⟩
  | succ n ih =>
    have hn := PinnedOuterReach.next hr
    obtain ⟨W0,he,hreach⟩ := ih (pinnedOuterStep L m defaultValue g W layers).1
      (pinnedOuterStep L m defaultValue g W layers).2 hn
    refine ⟨W0,?_,hreach⟩
    rw [Function.iterate_succ_apply,hstep n W layers hr]
    exact he

section PositiveDomain
variable [NeZero d]

/-- Literal raw/typed contract for a newly computed pinned layer. The returned
word is a genuine extended tuple, and its copied factor gives the exact
marginal, including zero-factor cancellation and the absent-class fallback. -/
theorem pinnedLayer_step_contract {m : Operation (Fin d)} (hm : IsMaltsev m)
    {n : ℕ} {W : Code (Fin d) (n+1)} (G : (Fin (n+1) → Fin d) → K)
    (hW : Correct W {x | G x ≠ 0}) (hEq : PreservesRowEquivalence m (rowFiber G))
    (evaluate : Tuple (Fin d) (n+1) → K) (he : ∀ x, evaluate x = G (view x))
    (defaultValue : Fin d) (x : Tuple (Fin d) n) (factors : List K) :
    let layer := buildPinnedLayer m W evaluate defaultValue
    let chosen := chooseRow m layer x
    ComplexityWeightedLayers.step (fun a b c => m (a,b,c)) (word x,factors) (encodeLayer layer) =
      (word (snocTuple x chosen.1),factors ++ [chosen.2]) ∧
    marginal G (view x) = G (view (snocTuple x chosen.1))*chosen.2 := by
  dsimp only
  refine ⟨step_encode m x factors _,?_⟩
  have hv := buildPinnedLayer_correct hm G hW hEq evaluate he defaultValue
  have hEq' : PreservesRowEquivalence m (labelFiber (rowSupport G) (fun x => tableLabel G (view x))) := by
    rw [labelFiber_rowFiber]; exact hEq
  have hclasses : ∀ a, Preserves m (rowFiber G a) := by
    intro a
    simpa only [labelFiber_rowFiber] using row_equivalence_fibers_preserves hm hEq' a
  exact chooseRow_factor hm G _ hv hclasses x

/-- Exact semantic contracts for the typed one-step data update. Both the support
witness and the raw ComputeF marginal invariant are computed, not assumed. -/
theorem pinnedOuterStep_correct (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (generatedSupports (L.mapValues σ)) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      Instance.Generated (L.mapValues σ) G → Preserves m (RowTypes.omegaRelation G).tuples)
    (defaultValue : Fin d) (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    {n : ℕ} (hn1 : n+1 ≤ g.vertices) (W : StoredCode d (n+1))
    (hW : Correct W.toCode {x | ComplexityCSPMarginalBounds.marginal L g hn1 x ≠ 0})
    (layers : List (ComplexityWeightedLayers.Layer K)) (hrep : RepresentsMarginal L m g hn1 layers) :
    Correct (pinnedOuterStep L m defaultValue g W layers).1.toCode
      {x | ComplexityCSPMarginalBounds.marginal L g (by omega : n ≤ g.vertices) x ≠ 0} ∧
    RepresentsMarginal L m g (by omega : n ≤ g.vertices)
      (pinnedOuterStep L m defaultValue g W layers).2 := by
  let G := ComplexityCSPMarginalBounds.marginal L g hn1
  have hG : Instance.Generated L G := generated_prefixMarginal L g hg (n+1) hn1
  have hEq := embedded_row_equivalence L σ hrow G hG
  obtain ⟨_,_,hclasses⟩ := embedded_row_hypotheses L σ hm hrow G hG
  let evaluate := fun x : Tuple (Fin d) (n+1) => ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g (word x) layers
  let layer := buildPinnedLayer m W.toCode evaluate defaultValue
  have hv : ValidLayer G layer := buildPinnedLayer_correct hm G hW hEq evaluate hrep defaultValue
  have heq : marginal G = ComplexityCSPMarginalBounds.marginal L g (by omega : n ≤ g.vertices) := by
    funext x
    exact (ComplexityCSPMarginalBounds.marginal_succ L g _ hn1 x).symm
  have hpres := embedded_support_preserves L σ hs (marginal G) (generated_marginal G hG)
  have hnext := marginalSupportCode_correct hm G layer hv hclasses hpres
  rw [heq] at hnext
  exact ⟨hnext,representsMarginal_prepend L hm g (by omega) hn1 layers hrep layer hv hclasses⟩

/-- Every genuinely reached context has the literal current marginal support
and suffix-layer interpretation. At dimension zero this is the final partition. -/
theorem pinnedOuterReach_correct (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (generatedSupports (L.mapValues σ)) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      Instance.Generated (L.mapValues σ) G → Preserves m (RowTypes.omegaRelation G).tuples)
    (defaultValue : Fin d) (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    {n : ℕ} {W : StoredCode d n} {layers : List (ComplexityWeightedLayers.Layer K)}
    (hr : PinnedOuterReach L m defaultValue g hg W layers) :
    ∃ hn : n ≤ g.vertices,
      Correct W.toCode {x | ComplexityCSPMarginalBounds.marginal L g hn x ≠ 0} ∧
      RepresentsMarginal L m g hn layers := by
  induction hr with
  | start =>
    have htables : ∀ i, Preserves m {x | L.value i x ≠ 0} := by
      intro i
      exact embedded_support_preserves L σ hs (L.value i) (language_value_generated L i)
    refine ⟨le_rfl,?_,representsMarginal_empty L m g hg⟩
    have hW := rawSupportWitness_correct L hm htables defaultValue g hg
    have heq : ComplexityCSPMarginalBounds.marginal L g le_rfl = ComplexityCSPCode.eval L g := by
      funext x; exact ComplexityCSPMarginalBounds.marginal_full L g x
    rwa [heq]
  | @next n W layers hr ih =>
    obtain ⟨hn,hW,hrep⟩ := ih
    exact ⟨by omega,pinnedOuterStep_correct L σ hm hs hrow defaultValue g hg hn W hW layers hrep⟩

section BitBounds
variable [Algebra ℚ K] {dimension : ℕ}

/-- Every produced layer in every reached context has one original-instance
polynomial bound, including layers with zero classes or zero sum factors. -/
theorem exists_pinnedOuter_layer_bits (L : Language (Fin d) K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ)
    {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (generatedSupports (L.mapValues σ)) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      Instance.Generated (L.mapValues σ) G → Preserves m (RowTypes.omegaRelation G).tuples)
    (hBO : JointBO (L.mapValues σ)) (defaultValue : Fin d) : ∃ p : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
      {n : ℕ} {W : StoredCode d n} {layers : List (ComplexityWeightedLayers.Layer K)},
      PinnedOuterReach L m defaultValue g hg W layers →
      ∀ layer ∈ layers, ((ComplexityWeightedLayers.layerCode basis).encode layer).length ≤
        p.eval (ComplexityCSPCode.encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_buildPinnedLayer_output_bound L basis
  refine ⟨p,?_⟩
  intro g hg n W layers hr
  induction hr with
  | start => simp
  | @next n W layers hr ih =>
    obtain ⟨hn,hW,hrep⟩ := pinnedOuterReach_correct L σ hm hs hrow defaultValue g hg hr
    let G := ComplexityCSPMarginalBounds.marginal L g hn
    have hG : Instance.Generated L G := generated_prefixMarginal L g hg (n+1) hn
    have hEq := embedded_row_equivalence L σ hrow G hG
    have hb : BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows G x a)) :=
      (JointBO.original (L.mapValues σ) hBO) n (fun x => σ (G x)) (Instance.generated_mapValues hG σ)
    intro layer he
    change layer ∈ _ :: layers at he
    rcases List.mem_cons.mp he with rfl | he
    · exact hp g hg n hn m hm W.toCode hW hEq _ hrep defaultValue σ hb
    · exact ih layer he

/-- Explicit outer-context polynomial: original instance, all suffix layers,
unary dimension and literal stored witness table/seed are charged. -/
noncomputable def outerContextPolynomial (d : ℕ) (layerPolynomial : Polynomial ℕ) : Polynomial ℕ :=
  6*Polynomial.X + 2*((6*layerPolynomial+3)*Polynomial.X+1) + storedPolynomial d + 4

omit [DecidableEq K] [NeZero d] in
/-- Exact codec arithmetic for an actual typed stored context. This lemma is
also usable for dimension zero and an absent support seed. -/
theorem storedContext_code_bound (basis : Module.Basis (Fin dimension) ℚ K)
    (g : ComplexityCSPCode.Code) {n : ℕ} (W : StoredCode d n)
    (layers : List (ComplexityWeightedLayers.Layer K)) (B : ℕ)
    (hB : (((ComplexityWeightedLayers.layerCode basis).list).encode layers).length ≤ B) :
    ((ComplexityTypeStackConcrete.contextCode basis).encode
      (ComplexityTypeStackConcrete.storedContext (g,layers) W)).length ≤
      4*(ComplexityCSPCode.encoding.encode g).length + 2*B + 2*n + (storedPolynomial d).eval n + 4 := by
  have hw := stored_code_bound W
  simp only [ComplexityTypeStackConcrete.contextCode,ComplexityTypeStackConcrete.storedContext,
    ComplexityTypeRowCallback.contextCode,BitEncoding.prod_length,BitEncoding.unaryNat_length]
  rw [BitEncoding.prod_length] at hw
  dsimp only at hw
  omega

/-- Uniform original-g cap for every context reached by the actual pinned outer
loop. Its proof uses literal data updates and actual marginal coefficient bounds;
no growing-state polynomial or output-size assumption is supplied. -/
theorem exists_pinnedOuter_context_bound (L : Language (Fin d) K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ)
    {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (generatedSupports (L.mapValues σ)) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      Instance.Generated (L.mapValues σ) G → Preserves m (RowTypes.omegaRelation G).tuples)
    (hBO : JointBO (L.mapValues σ)) (defaultValue : Fin d) : ∃ p : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
      {n : ℕ} {W : StoredCode d n} {layers : List (ComplexityWeightedLayers.Layer K)},
      PinnedOuterReach L m defaultValue g hg W layers →
      ((ComplexityTypeStackConcrete.contextCode basis).encode
        (ComplexityTypeStackConcrete.storedContext (g,layers) W)).length ≤
          p.eval (ComplexityCSPCode.encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_pinnedOuter_layer_bits L basis σ hm hs hrow hBO defaultValue
  refine ⟨outerContextPolynomial d p,?_⟩
  intro g hg n W layers hr
  let N := (ComplexityCSPCode.encoding.encode g).length
  have hN : g.vertices ≤ N := (Nat.le_add_right _ _).trans (ComplexityCSPCode.size_le_encoding_length g)
  have hlen := hr.length_eq
  have hn : n ≤ N := by omega
  have hlayers : layers.length ≤ N := by omega
  have hb := encoded_list_le (ComplexityWeightedLayers.layerCode basis) layers (p.eval N)
    (hp g hg hr)
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
end PositiveDomain
end ComplexCSP.WeightedMaltsev
