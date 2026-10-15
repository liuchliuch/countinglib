import ComplexCSP.Complexity.LabelExtensionCorrectness

/-! # Closed greedy label extension on preserved marginal-support restrictions

The space polynomial is selected from the proved actual stack bound. All
reconstruction, label, type-query and agreement hypotheses of the generic
correspondence theorem are discharged here from genuine marginal contexts.
-/
noncomputable section
namespace ComplexCSP.ComplexityLabelExtension
open PlanarHom PlanarHom.Complexity
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding WeightedMaltsev
open ComplexityWitnessPrimitives MaltsevTypeStack
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)

def restrictedSpace : Polynomial ℕ :=
  Classical.choose (MaltsevTypeStack.exists_correct_restricted_marginal_query L basis)

/-- The actual executable query uses this fixed proved polynomial on all raw
inputs, not a supplied restricted oracle or a lazily guarded callback. -/
def restrictedQuery (m : Fin d → Fin d → Fin d → Fin d) (q : Query K d) : Option (List ℕ) :=
  extendQuery L basis m (restrictedSpace L basis) q

theorem fp_restrictedQuery (m : Fin d → Fin d → Fin d → Fin d) :
    FP (queryCode basis) (ComplexityTypeStackMachines.optionCode wordCode)
      (restrictedQuery L basis m) := fp_query L basis m (restrictedSpace L basis)

/-- The same chosen polynomial computes the exact initial label/cache query. -/
theorem restrictedTypeQuery_correct (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (k : ℕ) (hk1 : k+1≤g.vertices) (R : Set (Fin k → Fin d))
    (hsub : R⊆rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1))
    (m : Operation (Fin d)) (hm : IsMaltsev m) (W : StoredCode d k)
    (hW : Correct W.toCode R) (hR : Preserves m R)
    (hTP : TypesPartition R (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)))
    (σ : K →+* ℂ)
    (hBO : BlockOrthogonality.BlockOrthogonal
      (fun x a => σ (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) x a)))
    (layers : List (ComplexityWeightedLayers.Layer K)) (hrep : RepresentsMarginal L m g hk1 layers)
    (fuel len : ℕ) (hdepth : len+fuel=k) (target : Tuple (Fin d) k) :
    ComplexityTypeQuery.executeWithSpace L basis (curried m) (restrictedSpace L basis)
      (ComplexityTypeStackConcrete.storedContext (g,layers) W,len,word target)=
      materializedTypeSearch m W.toCode
        (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x))
        fuel len target [] := by
  have h := (Classical.choose_spec (MaltsevTypeStack.exists_correct_restricted_marginal_query L basis))
    g hg k hk1 R hsub m hm W hW hR hTP σ hBO layers hrep fuel len hdepth target
  unfold ComplexityTypeQuery.executeWithSpace ComplexityTypeQuery.prepare
  change ((ComplexityTypeStackExecution.run L basis (curried m)
    (restrictedSpace L basis) (MaltsevTypeStack.transitionPolynomial d)
    (ComplexityTypeStackConcrete.storedContext (g,layers) W,callState len (word target) [] [])).returnedLabels,
    (ComplexityTypeStackExecution.run L basis (curried m)
    (restrictedSpace L basis) (MaltsevTypeStack.transitionPolynomial d)
    (ComplexityTypeStackConcrete.storedContext (g,layers) W,callState len (word target) [] [])).cache)=_
  exact congrArg (fun x : MaltsevTypeStack.State (RowLabel K d) => (x.returnedLabels,x.cache)) h

/-- Exact agreement with the typed greedy algorithm on arbitrary actually
preserved restrictions, including the literal coordinate-pin witnesses. -/
theorem restrictedQuery_correct (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (k : ℕ) (hk1 : k+1≤g.vertices) (R : Set (Fin k → Fin d))
    (hsub : R⊆rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1))
    (m : Operation (Fin d)) (hm : IsMaltsev m) (W : StoredCode d k)
    (hW : Correct W.toCode R) (hR : Preserves m R)
    (hTP : TypesPartition R (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)))
    (σ : K →+* ℂ)
    (hBO : BlockOrthogonality.BlockOrthogonal
      (fun x a => σ (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) x a)))
    (layers : List (ComplexityWeightedLayers.Layer K)) (hrep : RepresentsMarginal L m g hk1 layers)
    (wanted : RowLabel K d) (fuel len : ℕ) (hdepth : len+fuel=k) (target : Tuple (Fin d) k) :
    restrictedQuery L basis (curried m)
      (ComplexityTypeStackConcrete.storedContext (g,layers) W,wanted,len,word target)=
      (labelExtension m W.toCode
        (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x))
        wanted fuel len target).map word := by
  apply extendQuery_stored L basis m (restrictedSpace L basis) (g,layers) W
    (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x))
  · exact label_of_representsMarginal L m g hk1 layers hrep
  · intro fuel len hdepth target
    exact congrArg Prod.fst (restrictedTypeQuery_correct L basis g hg k hk1 R hsub m hm W hW hR hTP
      σ hBO layers hrep fuel len hdepth target)
  · exact hdepth

end ComplexCSP.ComplexityLabelExtension
