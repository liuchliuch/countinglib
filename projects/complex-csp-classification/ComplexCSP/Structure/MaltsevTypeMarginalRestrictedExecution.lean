import ComplexCSP.Structure.MaltsevTypeMarginalStackExecution
import ComplexCSP.Structure.MaltsevTypeRestriction

/-! # Closed marginal queries on actual preserved support restrictions

The row callback remains the original literal marginal callback. Unary pinning
changes only the stored support witness. Its label range and bit cap are still
derived from the original marginal's genuine BO row classes.
-/
namespace ComplexCSP.MaltsevTypeStack
open MaltsevWitness MaltsevRelations WeightedMaltsev ComplexityWitnessEncoding
open ComplexityCSPMarginalBounds ComplexityCSPMarginalRowBounds ComplexityCSPMarginalCacheBounds
open ComplexityCSPCode ComplexityTypeStackMachines
open PlanarHom PlanarHom.Complexity PlanarHom.MachineComposition
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}

theorem exists_restricted_marginal_stack_output_bound (L : Language (Fin d) K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) : ∃ p : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code), Valid L g →
    ∀ (k : ℕ) (hk1 : k+1 ≤ g.vertices) (R : Set (Fin k → Fin d)),
      R ⊆ rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1) →
    ∀ (m : Operation (Fin d)) (W : StoredCode d k),
      Correct W.toCode R →
      Preserves m R →
    ∀ (σ : K →+* ℂ),
      BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) x a)) →
    ∀ (labelRaw : List ℕ → RowLabel K d),
      (∀ x, labelRaw (word x) = tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)) →
    ∀ (len : ℕ), len ≤ k → ∀ (target : Tuple (Fin d) k) (state : State (RowLabel K d)) (t : ℕ),
      t ≤ 2*(1+d*((k+1)*d)) →
      Runs (step k (List.range d) (storedReconstruct m W) labelRaw)
        (callState len (word target) [] []) state t →
      ((stateCode (labelEncoding basis d)).encode state).length ≤ p.eval (encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_normalized_marginal_bounds L basis
  refine ⟨statePolynomial d p,?_⟩
  intro g hg k hk1 R hsub m W hW hR σ hBO labelRaw hlab len hlen target state t ht hrun
  let G := ComplexityCSPMarginalBounds.marginal L g hk1
  let U := presentLabels G
  let N := (encoding.encode g).length
  have hlabels : ∀ a ∈ U, ((labelEncoding basis d).encode a).length ≤ p.eval N := by
    intro a ha
    obtain ⟨x,hx⟩ := present_label_realized G a ha
    rw [← hx]
    exact (hp g hg k hk1 x).1
  have hU : ∀ x ∈ R, tableLabel G (view (Vector.ofFn x)) ∈ U := by
    intro x hx
    simpa only [view_ofFn] using tableLabel_mem_present G x (hsub hx)
  have hs := stored_reached_code_bound (labelEncoding basis d) hR hW
    (fun x => tableLabel G (view x)) labelRaw hlab U hU (p.eval N) hlabels len hlen target hrun
  have hn : k ≤ N := by
    have hh := size_le_encoding_length g
    dsimp [N]
    omega
  have hu : U.card ≤ d := presentLabels_card_le G σ hBO
  have ht' : t ≤ 2*(1+d*((N+1)*d)) := ht.trans (by gcongr)
  exact hs.trans (by
    rw [statePolynomial_eval]
    exact stateBound_mono hn hu (Nat.le_refl _) ht')


theorem exists_correct_restricted_marginal_query (L : Language (Fin d) K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) : ∃ space : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code), Valid L g →
    ∀ (k : ℕ) (hk1 : k+1 ≤ g.vertices) (R : Set (Fin k → Fin d)),
      R ⊆ rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1) →
    ∀ (m : Operation (Fin d)), IsMaltsev m →
    ∀ (W : StoredCode d k),
      Correct W.toCode R →
      Preserves m R →
      TypesPartition R
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
  obtain ⟨space,hspace⟩ := exists_restricted_marginal_stack_output_bound L basis
  refine ⟨space,?_⟩
  intro g hg k hk1 R hsub m hm W hW hR hTP σ hBO layers hrep fuel len hdepth target
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
  have hU : ∀ x ∈ R, typedLabel (Vector.ofFn x) ∈ presentLabels G := by
    intro x hx
    simpa only [typedLabel,view_ofFn] using tableLabel_mem_present G x (hsub hx)
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
    have hs := hspace g hg k hk1 R hsub m W hW hR σ hBO rawLabel hlab len (by omega) target state t
      (ht.trans hcount) htrace
    exact hs.trans (natPolynomial_monotone space hN)


end ComplexCSP.MaltsevTypeStack
