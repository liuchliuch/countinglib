import ComplexCSP.Complexity.PinnedOuterCorrectness
import ComplexCSP.Structure.WeightedMaltsevPinnedDegreeOuter

/-! # Actual capped outer evaluation under positive DegreeJointBO

The runtime machine, initialization, cap mechanism and final ComputeF are the
same as in the ordinary theorem. Every semantic and cap premise is discharged
on the genuine degree-divisible family, without unrestricted JointBO.
-/
namespace ComplexCSP.ComplexityPinnedOuter
open MaltsevWitness MaltsevRelations WeightedMaltsev ComplexityWitnessEncoding
open ComplexitySupportWitnessPrimitives ComplexityPinnedClass ComplexityLabelExtension
open PlanarHom PlanarHom.Complexity PlanarHom.MachineComposition
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ} [NeZero d]
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)

theorem iterate_reached_degree (σ : K →+* ℂ) {δ : ℕ} (hδ : 0 < δ) {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (degreeGeneratedSupports (L.mapValues σ) δ) m)
    (hrow : ∀ (n : ℕ), 0<n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      DegreeGenerated (L.mapValues σ) δ G → Preserves m (RowTypes.omegaRelation G).tuples)
    (hBO : DegreeJointBO (L.mapValues σ) δ) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (hdegree : (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ) (i : ℕ) :
    ∃ (n : ℕ) (W : StoredCode d n) (layers : List (ComplexityWeightedLayers.Layer K)),
      (advance L basis m (restrictedSpace L basis) defaultValue)^[i]
        (packContext (g,[]) (rawSupportWitness L m defaultValue g hg).toCode) = packContext (g,layers) W.toCode ∧
      PinnedOuterReach L m defaultValue g hg W layers ∧ n = g.vertices-i := by
  apply iterate_reached_of_step L basis m defaultValue g hg _ i
  intro n W layers hr
  obtain ⟨hn,hW,hrep⟩ := pinnedOuterReach_correct_degree L σ hδ hm hs hrow defaultValue g hg hdegree hr
  let G := ComplexityCSPMarginalBounds.marginal L g hn
  have hG : DegreeGenerated L δ G := degree_generated_prefixMarginal L g hg hdegree (n+1) hn
  have hEq := embedded_degree_row_equivalence L σ hrow G hG
  have hb : BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows G x a)) :=
    (DegreeJointBO.original (L.mapValues σ) δ hBO) n (fun x => σ (G x)) (hG.mapValues σ)
  exact advance_packContext L basis m hm defaultValue g hg hn W hW σ hb hEq layers hrep

/-- One actual outer cap works on every valid instance of the fixed language.
The bound is evaluated on the literal initial encoded context, and the actual
final ComputeF machine returns the partition value. -/
theorem exists_evaluate_correct_degree (σ : K →+* ℂ) {δ : ℕ} (hδ : 0 < δ) {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (degreeGeneratedSupports (L.mapValues σ) δ) m)
    (hrow : ∀ (n : ℕ), 0<n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      DegreeGenerated (L.mapValues σ) δ G → Preserves m (RowTypes.omegaRelation G).tuples)
    (hBO : DegreeJointBO (L.mapValues σ) δ) (defaultValue : Fin d) : ∃ outerSpace : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g),
      (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ →
      evaluate L basis m (restrictedSpace L basis) defaultValue outerSpace
        (packContext (g,[]) (rawSupportWitness L m defaultValue g hg).toCode) = ComplexityCSPCode.partition L g := by
  obtain ⟨space,hspace⟩ := exists_pinnedOuter_context_bound_degree L basis σ hδ hm hs hrow hBO defaultValue
  refine ⟨space,?_⟩
  intro g hg hdegree
  let initial : ComplexityPinnedClass.Context K d := packContext (g,[]) (rawSupportWitness L m defaultValue g hg).toCode
  let N := ((BitEncoding.nat.prod (ComplexityPinnedClass.contextCode basis)).encode (0,initial)).length
  have hN := original_length_le_outerInput basis g (rawSupportWitness L m defaultValue g hg) []
  have hdim : g.vertices ≤ N := dimension_le_outerInput basis g (rawSupportWitness L m defaultValue g hg) []
  have hcap : ∀ i, i ≤ N →
      ((ComplexityPinnedClass.contextCode basis).encode
        ((advance L basis m (restrictedSpace L basis) defaultValue)^[i] initial)).length ≤ space.eval N := by
    intro i _
    obtain ⟨n,W,layers,he,hr,_⟩ := iterate_reached_degree L basis σ hδ hm hs hrow hBO defaultValue g hg hdegree i
    rw [he,packed_context_length]
    exact (hspace g hg hdegree hr).trans (natPolynomial_monotone space hN)
  unfold evaluate
  rw [execute_eq_iterate L basis m (restrictedSpace L basis) defaultValue space initial hcap]
  obtain ⟨n,W,layers,he,hr,hn⟩ := iterate_reached_degree L basis σ hδ hm hs hrow hBO defaultValue g hg hdegree N
  rw [he]
  have hn0 : n=0 := by omega
  cases hn0
  obtain ⟨hzero,_,hrep⟩ := pinnedOuterReach_correct_degree L σ hδ hm hs hrow defaultValue g hg hdegree hr
  have hfinal := hrep (Vector.ofFn Fin.elim0)
  simpa [finish,packContext,ComplexityCSPMarginalBounds.marginal_empty,word,
    Vector.toList_ofFn,List.ofFn_zero] using hfinal

/-- Genuine degree-family BO supplies the fixed common operation and a proved
cap for the closed actual raw evaluator on its divisible-degree promise. -/
theorem degreeJointBO_actual_evaluator [Nonempty (Fin d)] (σ : K →+* ℂ) {δ : ℕ} (hδ : 0 < δ)
    (hAlg : ∀ i a, IsAlgebraic ℚ ((L.mapValues σ).value i a)) (hBO : DegreeJointBO (L.mapValues σ) δ)
    (defaultValue : Fin d) : ∃ (m : Operation (Fin d)) (outerSpace : Polynomial ℕ), IsMaltsev m ∧
    ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g),
      (ComplexityCSPCode.toInstance L g hg).DegreeDivisible δ →
      evaluate L basis m (restrictedSpace L basis) defaultValue outerSpace
        (packContext (g,[]) (rawSupportWitness L m defaultValue g hg).toCode) = ComplexityCSPCode.partition L g := by
  obtain ⟨m,hm,hs,hrow⟩ := DegreeStructuralCollapse.common_support_and_row_maltsev (L.mapValues σ) δ hAlg hBO
  obtain ⟨space,hspace⟩ := exists_evaluate_correct_degree L basis σ hδ hm hs hrow hBO defaultValue
  exact ⟨m,space,hm,hspace⟩


end ComplexCSP.ComplexityPinnedOuter
