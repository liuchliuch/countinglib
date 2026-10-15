import ComplexCSP.Complexity.PinnedOuterMachine
import ComplexCSP.Complexity.PinnedLayerCorrectness
import ComplexCSP.Structure.WeightedMaltsevPinnedOuter

/-! # Exact correctness of the actual capped pinned outer machine

Every raw step is identified with its literal typed constructor update. The
original-instance polynomial bounds every uncapped intermediate; monotonicity
then proves the actual outer cap never triggers on valid source instances.
-/
namespace ComplexCSP.ComplexityPinnedOuter
open MaltsevWitness MaltsevRelations WeightedMaltsev ComplexityWitnessEncoding
open ComplexitySupportWitnessPrimitives ComplexityPinnedClass ComplexityLabelExtension
open PlanarHom PlanarHom.Complexity PlanarHom.MachineComposition
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)

omit [Field K] [DecidableEq K] [Algebra ℚ K] in
@[simp] theorem packContext_stored_val {n : ℕ} (base : ComplexityTypeRowCallback.Context K)
    (W : StoredCode d n) : (packContext base W.toCode).val = ComplexityTypeStackConcrete.storedContext base W := by
  simp only [packContext,ComplexityTypeStackConcrete.storedContext,encodeCode_stored]

omit [DecidableEq K] in
theorem packed_context_length {n : ℕ} (base : ComplexityTypeRowCallback.Context K) (W : StoredCode d n) :
    ((ComplexityPinnedClass.contextCode basis).encode (packContext base W.toCode)).length =
      ((ComplexityTypeStackConcrete.contextCode basis).encode (ComplexityTypeStackConcrete.storedContext base W)).length := by
  simp only [ComplexityPinnedClass.contextCode,BitEncoding.restrict,packContext_stored_val]

/-- The actual layer program and actual marginal-support update give the exact
one-step typed data, with all internal query agreement hypotheses discharged. -/
theorem advance_packContext (m : Operation (Fin d)) (hm : IsMaltsev m) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    {n : ℕ} (hn1 : n+1 ≤ g.vertices) (W : StoredCode d (n+1))
    (hW : Correct W.toCode {x | ComplexityCSPMarginalBounds.marginal L g hn1 x ≠ 0})
    (σ : K →+* ℂ)
    (hBO : BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows (ComplexityCSPMarginalBounds.marginal L g hn1) x a)))
    (hEq : PreservesRowEquivalence m (rowFiber (ComplexityCSPMarginalBounds.marginal L g hn1)))
    (layers : List (ComplexityWeightedLayers.Layer K)) (hrep : RepresentsMarginal L m g hn1 layers) :
    advance L basis m (restrictedSpace L basis) defaultValue (packContext (g,layers) W.toCode) =
      packContext (g,(pinnedOuterStep L m defaultValue g W layers).2)
        (pinnedOuterStep L m defaultValue g W layers).1.toCode := by
  have hl := ComplexityPinnedLayer.compile_eq_buildPinnedLayer L basis m defaultValue g hg n hn1 hm σ hBO
    layers hrep W.toCode hW hEq
  apply Subtype.ext
  simp only [advance,packContext_stored_val,ComplexityTypeStackConcrete.storedContext,
    Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte]
  change update (curried m) ((packContext (g,layers) W.toCode).val,
      ComplexityPinnedLayer.compile L basis m defaultValue (packContext (g,layers) W.toCode)) = _
  rw [hl,packContext_stored_val]
  exact update_encode L m defaultValue g W layers

/-- Every uncapped iterate is a genuinely reached typed context; the dimension
is the truncated original dimension minus the iteration count and freezes at 0. -/
theorem iterate_reached_of_step (m : Operation (Fin d)) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (hstep : ∀ (n : ℕ) (W : StoredCode d (n+1)) (layers : List (ComplexityWeightedLayers.Layer K)),
      PinnedOuterReach L m defaultValue g hg W layers →
      advance L basis m (restrictedSpace L basis) defaultValue (packContext (g,layers) W.toCode) =
        packContext (g,(pinnedOuterStep L m defaultValue g W layers).2)
          (pinnedOuterStep L m defaultValue g W layers).1.toCode)
    (i : ℕ) : ∃ (n : ℕ) (W : StoredCode d n) (layers : List (ComplexityWeightedLayers.Layer K)),
      (advance L basis m (restrictedSpace L basis) defaultValue)^[i]
        (packContext (g,[]) (rawSupportWitness L m defaultValue g hg).toCode) = packContext (g,layers) W.toCode ∧
      PinnedOuterReach L m defaultValue g hg W layers ∧ n = g.vertices-i := by
  induction i with
  | zero => exact ⟨g.vertices,_,[],rfl,PinnedOuterReach.start,by omega⟩
  | succ i ih =>
    obtain ⟨n,W,layers,he,hr,hn⟩ := ih
    rw [Function.iterate_succ_apply',he]
    cases n with
    | zero =>
      refine ⟨0,W,layers,?_,hr,by omega⟩
      apply advance_zero
      rfl
    | succ n =>
      refine ⟨n,(pinnedOuterStep L m defaultValue g W layers).1,
        (pinnedOuterStep L m defaultValue g W layers).2,hstep n W layers hr,PinnedOuterReach.next hr,by omega⟩

omit [DecidableEq K] in
theorem original_length_le_outerInput (g : ComplexityCSPCode.Code) {n : ℕ}
    (W : StoredCode d n) (layers : List (ComplexityWeightedLayers.Layer K)) :
    (ComplexityCSPCode.encoding.encode g).length ≤
      ((BitEncoding.nat.prod (ComplexityPinnedClass.contextCode basis)).encode
        (0,packContext (g,layers) W.toCode)).length := by
  simp only [ComplexityPinnedClass.contextCode,BitEncoding.restrict,BitEncoding.prod_length,
    packContext_stored_val,ComplexityTypeStackConcrete.contextCode,ComplexityTypeStackConcrete.storedContext,
    ComplexityTypeRowCallback.contextCode,BitEncoding.prod_length]
  omega

omit [DecidableEq K] in
theorem dimension_le_outerInput (g : ComplexityCSPCode.Code) {n : ℕ}
    (W : StoredCode d n) (layers : List (ComplexityWeightedLayers.Layer K)) :
    n ≤ ((BitEncoding.nat.prod (ComplexityPinnedClass.contextCode basis)).encode
      (0,packContext (g,layers) W.toCode)).length := by
  simp only [ComplexityPinnedClass.contextCode,BitEncoding.restrict,BitEncoding.prod_length,
    packContext_stored_val,ComplexityTypeStackConcrete.contextCode,ComplexityTypeStackConcrete.storedContext,
    ComplexityTypeRowCallback.contextCode,BitEncoding.prod_length,BitEncoding.unaryNat_length]
  omega

section PositiveDomain
variable [NeZero d]

/-- The ordinary source hypotheses instantiate every one-step contract. -/
theorem iterate_reached (σ : K →+* ℂ) {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (generatedSupports (L.mapValues σ)) m)
    (hrow : ∀ (n : ℕ), 0<n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      Instance.Generated (L.mapValues σ) G → Preserves m (RowTypes.omegaRelation G).tuples)
    (hBO : JointBO (L.mapValues σ)) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) (i : ℕ) :
    ∃ (n : ℕ) (W : StoredCode d n) (layers : List (ComplexityWeightedLayers.Layer K)),
      (advance L basis m (restrictedSpace L basis) defaultValue)^[i]
        (packContext (g,[]) (rawSupportWitness L m defaultValue g hg).toCode) = packContext (g,layers) W.toCode ∧
      PinnedOuterReach L m defaultValue g hg W layers ∧ n = g.vertices-i := by
  apply iterate_reached_of_step L basis m defaultValue g hg _ i
  intro n W layers hr
  obtain ⟨hn,hW,hrep⟩ := pinnedOuterReach_correct L σ hm hs hrow defaultValue g hg hr
  let G := ComplexityCSPMarginalBounds.marginal L g hn
  have hG : Instance.Generated L G := generated_prefixMarginal L g hg (n+1) hn
  have hEq := embedded_row_equivalence L σ hrow G hG
  have hb : BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows G x a)) :=
    (JointBO.original (L.mapValues σ) hBO) n (fun x => σ (G x)) (Instance.generated_mapValues hG σ)
  exact advance_packContext L basis m hm defaultValue g hg hn W hW σ hb hEq layers hrep

/-- One actual outer cap works on every valid instance of the fixed language.
The bound is evaluated on the literal initial encoded context, and the actual
final ComputeF machine returns the partition value. -/
theorem exists_evaluate_correct (σ : K →+* ℂ) {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (generatedSupports (L.mapValues σ)) m)
    (hrow : ∀ (n : ℕ), 0<n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      Instance.Generated (L.mapValues σ) G → Preserves m (RowTypes.omegaRelation G).tuples)
    (hBO : JointBO (L.mapValues σ)) (defaultValue : Fin d) : ∃ outerSpace : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g),
      evaluate L basis m (restrictedSpace L basis) defaultValue outerSpace
        (packContext (g,[]) (rawSupportWitness L m defaultValue g hg).toCode) = ComplexityCSPCode.partition L g := by
  obtain ⟨space,hspace⟩ := exists_pinnedOuter_context_bound L basis σ hm hs hrow hBO defaultValue
  refine ⟨space,?_⟩
  intro g hg
  let initial : ComplexityPinnedClass.Context K d := packContext (g,[]) (rawSupportWitness L m defaultValue g hg).toCode
  let N := ((BitEncoding.nat.prod (ComplexityPinnedClass.contextCode basis)).encode (0,initial)).length
  have hN := original_length_le_outerInput basis g (rawSupportWitness L m defaultValue g hg) []
  have hdim : g.vertices ≤ N := dimension_le_outerInput basis g (rawSupportWitness L m defaultValue g hg) []
  have hcap : ∀ i, i ≤ N →
      ((ComplexityPinnedClass.contextCode basis).encode
        ((advance L basis m (restrictedSpace L basis) defaultValue)^[i] initial)).length ≤ space.eval N := by
    intro i _
    obtain ⟨n,W,layers,he,hr,_⟩ := iterate_reached L basis σ hm hs hrow hBO defaultValue g hg i
    rw [he,packed_context_length]
    exact (hspace g hg hr).trans (natPolynomial_monotone space hN)
  unfold evaluate
  rw [execute_eq_iterate L basis m (restrictedSpace L basis) defaultValue space initial hcap]
  obtain ⟨n,W,layers,he,hr,hn⟩ := iterate_reached L basis σ hm hs hrow hBO defaultValue g hg N
  rw [he]
  have hn0 : n=0 := by omega
  cases hn0
  obtain ⟨hzero,_,hrep⟩ := pinnedOuterReach_correct L σ hm hs hrow defaultValue g hg hr
  have hfinal := hrep (Vector.ofFn Fin.elim0)
  simpa [finish,packContext,ComplexityCSPMarginalBounds.marginal_empty,word,
    Vector.toList_ofFn,List.ofFn_zero] using hfinal

/-- Genuine global BO supplies both the fixed common operation and a proved
cap for the closed actual raw evaluator. -/
theorem jointBO_actual_evaluator [Nonempty (Fin d)] (σ : K →+* ℂ)
    (hAlg : ∀ i a, IsAlgebraic ℚ ((L.mapValues σ).value i a)) (hBO : JointBO (L.mapValues σ))
    (defaultValue : Fin d) : ∃ (m : Operation (Fin d)) (outerSpace : Polynomial ℕ), IsMaltsev m ∧
    ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g),
      evaluate L basis m (restrictedSpace L basis) defaultValue outerSpace
        (packContext (g,[]) (rawSupportWitness L m defaultValue g hg).toCode) = ComplexityCSPCode.partition L g := by
  obtain ⟨m,hm,hs,hrow⟩ := RowEquivalenceRealization.common_support_and_row_maltsev (L.mapValues σ) hAlg hBO
  obtain ⟨space,hspace⟩ := exists_evaluate_correct L basis σ hm hs hrow hBO defaultValue
  exact ⟨m,space,hm,hspace⟩

end PositiveDomain
end ComplexCSP.ComplexityPinnedOuter
