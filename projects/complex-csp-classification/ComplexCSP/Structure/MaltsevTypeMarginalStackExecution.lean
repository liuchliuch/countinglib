import ComplexCSP.Structure.MaltsevTypeMarginalStackBounds
import ComplexCSP.Structure.WeightedMaltsevSuffix
import ComplexCSP.Complexity.TypeStackExecution

/-! # Exact actual FP stack queries on constructed marginal contexts

This closes the bounded-program bridge: the raw program's reconstruction,
ComputeF, normalization, codecs, cap and iteration budget are all actual
implementations. Its result is the exact materialized label list and cache.
-/
namespace ComplexCSP.MaltsevTypeStack
open MaltsevWitness MaltsevRelations WeightedMaltsev ComplexityWitnessEncoding
open ComplexityCSPMarginalBounds ComplexityCSPMarginalRowBounds
open ComplexityCSPCode ComplexityTypeStackMachines
open PlanarHom PlanarHom.Complexity PlanarHom.MachineComposition
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}

noncomputable def transitionPolynomial (d : ℕ) : Polynomial ℕ :=
  2*(1+Polynomial.C d*((Polynomial.X+1)*Polynomial.C d))

@[simp] theorem transitionPolynomial_eval (d N : ℕ) :
    (transitionPolynomial d).eval N = 2*(1+d*((N+1)*d)) := by simp [transitionPolynomial]

omit [DecidableEq K] in
/-- The original raw instance is a literal field of the prepared context/input;
its length is therefore bounded by that prepared input's word length. -/
theorem original_length_le_prepared (basis : Module.Basis (Fin dimension) ℚ K)
    (g : ComplexityCSPCode.Code) (layers : List (ComplexityWeightedLayers.Layer K))
    {k : ℕ} (W : StoredCode d k) (start : State (RowLabel K d)) :
    (encoding.encode g).length ≤
      ((ComplexityTypeStackExecution.inputCode (d:=d) basis).encode
        (ComplexityTypeStackConcrete.storedContext (g,layers) W,start)).length := by
  simp only [ComplexityTypeStackExecution.inputCode,ComplexityTypeStackConcrete.contextCode,
    ComplexityTypeStackConcrete.storedContext,ComplexityTypeRowCallback.contextCode,
    BitEncoding.prod_length]
  omega

/-- One fixed polynomial cap works for every genuine marginal query. The time
polynomial is explicit and both budgets are evaluated on the actual prepared
input word, with no evolving-state size or evaluation oracle assumption. -/
theorem exists_correct_marginal_query (L : Language (Fin d) K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) : ∃ space : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code), Valid L g →
    ∀ (k : ℕ) (hk1 : k+1 ≤ g.vertices) (m : Operation (Fin d)), IsMaltsev m →
    ∀ (W : StoredCode d k),
      Correct W.toCode (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1)) →
      Preserves m (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1)) →
      TypesPartition (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1))
        (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)) →
    ∀ (σ : K →+* ℂ),
      BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) x a)) →
    ∀ (layers : List (ComplexityWeightedLayers.Layer K)), RepresentsMarginal L m g hk1 layers →
    ∀ (fuel len : ℕ), len+fuel=k → ∀ (target : Tuple (Fin d) k),
      ComplexityTypeStackExecution.run L basis (fun a b c => m (a,b,c)) space (transitionPolynomial d)
        (ComplexityTypeStackConcrete.storedContext (g,layers) W,callState len (word target) [] []) =
      returnState len (word target)
        (materializedTypeSearch m W.toCode
          (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)) fuel len target []).1 []
        (materializedTypeSearch m W.toCode
          (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)) fuel len target []).2 := by
  obtain ⟨space,hspace⟩ := exists_marginal_stack_output_bound L basis
  refine ⟨space,?_⟩
  intro g hg k hk1 m hm W hW hR hTP σ hBO layers hrep fuel len hdepth target
  let G := ComplexityCSPMarginalBounds.marginal L g hk1
  let typedLabel := fun x : Tuple (Fin d) k => tableLabel G (view x)
  let rawLabel := ComplexityTypeRowCallback.label L (fun a b c => m (a,b,c)) (g,layers)
  let context := ComplexityTypeStackConcrete.storedContext (g,layers) W
  let start : State (RowLabel K d) := callState len (word target) [] []
  let result := materializedTypeSearch m W.toCode typedLabel fuel len target []
  let finish : State (RowLabel K d) := returnState len (word target) result.1 [] result.2
  let count := (search k (List.range d) (storedReconstruct m W) rawLabel fuel len (word target) []).2
  have hlab : ∀ x, rawLabel (word x) = typedLabel x :=
    label_of_representsMarginal L m g hk1 layers hrep
  have hstep : (fun state => ComplexityTypeStackConcrete.step L (fun a b c => m (a,b,c)) (context,state)) =
      MaltsevTypeStack.step k (List.range d) (storedReconstruct m W) rawLabel := by
    funext state
    unfold ComplexityTypeStackConcrete.step
    rw [contextualStep_correct]
    rfl
  have hr : Runs (fun state => ComplexityTypeStackConcrete.step L (fun a b c => m (a,b,c)) (context,state))
      start finish count := by
    rw [hstep]
    exact stored_materialized_runs m W typedLabel rawLabel hlab fuel len hdepth target [] []
  have hh : ComplexityTypeStackConcrete.step L (fun a b c => m (a,b,c)) (context,finish) = none := by
    change (fun state => ComplexityTypeStackConcrete.step L (fun a b c => m (a,b,c)) (context,state)) finish = none
    rw [hstep]
    exact step_halt _ _ _ _ _ _ _ _
  have hU : ∀ x ∈ rowSupport G, typedLabel (Vector.ofFn x) ∈ presentLabels G := by
    intro x hx
    simpa only [typedLabel,view_ofFn] using tableLabel_mem_present G x hx
  have hcount : count ≤ 2*(1+d*((k+1)*d)) := by
    have hb := materialized_transition_bound hm hR hW typedLabel hTP (storedReconstruct m W) rawLabel
      (storedReconstruct_word m W) hlab fuel len hdepth target (presentLabels G) hU
    have hu := presentLabels_card_le G σ hBO
    exact (Nat.le_succ count).trans (hb.trans (by gcongr))
  have hN := original_length_le_prepared basis g layers W start
  have hkN : k ≤ ((ComplexityTypeStackExecution.inputCode (d:=d) basis).encode (context,start)).length := by
    have hgN := size_le_encoding_length g
    dsimp only [context] at *
    omega
  apply ComplexityTypeStackExecution.run_correct L basis (fun a b c => m (a,b,c)) space
    (transitionPolynomial d) context start finish count hr hh
  · rw [transitionPolynomial_eval]
    exact hcount.trans (by gcongr)
  · intro state t ht htrace
    rw [hstep] at htrace
    have hs := hspace g hg k hk1 m W hW hR σ hBO rawLabel hlab len (by omega) target state t
      (ht.trans hcount) htrace
    exact hs.trans (natPolynomial_monotone space hN)

end ComplexCSP.MaltsevTypeStack
