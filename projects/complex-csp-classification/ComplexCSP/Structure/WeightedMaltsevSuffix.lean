import ComplexCSP.Structure.WeightedMaltsevTower
import ComplexCSP.Complexity.TypeRowCallback

/-! # Actual ComputeF on suffix layers and prefix marginals

The invariant here concerns the concrete raw executor initialized by the
original CSP product. Prepending one actually constructed class layer performs
one exact marginalization. It supplies the row callback identity used by the
bounded continuation-stack constructor.
-/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness ComplexityWitnessEncoding
variable {K : Type} [Field K] [DecidableEq K] {d s : ℕ}

omit [DecidableEq K] in
theorem fold_layers_factors (m : Operation (Fin d))
    (layers : List (ComplexityWeightedLayers.Layer K)) (xs : List ℕ) (factors : List K) :
    layers.foldl (ComplexityWeightedLayers.step (fun a b c => m (a,b,c))) (xs,factors) =
      (let result := layers.foldl (ComplexityWeightedLayers.step (fun a b c => m (a,b,c))) (xs,[])
       (result.1,factors ++ result.2)) := by
  induction layers generalizing xs factors with
  | nil => simp
  | cons layer layers ih =>
    simp only [List.foldl_cons,ComplexityWeightedLayers.step,List.nil_append]
    rw [ih _ (factors ++ [_]),ih _ [_]]
    simp [List.append_assoc]

section PositiveDomain
variable [NeZero d]

omit [DecidableEq K] in
theorem execute_prepend_layer (L : Language (Fin d) K (Fin s)) (m : Operation (Fin d))
    (g : ComplexityCSPCode.Code) {k : ℕ} (x : Tuple (Fin d) k) (layer : Layer K d k)
    (layers : List (ComplexityWeightedLayers.Layer K)) :
    ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g (word x) (encodeLayer layer :: layers) =
      ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g
        (word (snocTuple x (chooseRow m layer x).1)) layers * (chooseRow m layer x).2 := by
  simp only [ComplexityWeightedLayers.execute,List.foldl_cons,step_encode,List.nil_append]
  rw [fold_layers_factors m layers _ [(chooseRow m layer x).2]]
  simp only [ComplexityWeightedLayers.finish,List.prod_append,List.prod_singleton]
  ring

/-- Every typed prefix is evaluated by the actual raw executor as its literal
CSP marginal. Layers and original g are ordinary immutable input data. -/
def RepresentsMarginal (L : Language (Fin d) K (Fin s)) (m : Operation (Fin d))
    (g : ComplexityCSPCode.Code) {k : ℕ} (hk : k ≤ g.vertices)
    (layers : List (ComplexityWeightedLayers.Layer K)) : Prop :=
  ∀ x : Tuple (Fin d) k,
    ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g (word x) layers =
      ComplexityCSPMarginalBounds.marginal L g hk (view x)

omit [DecidableEq K] [NeZero d] in
theorem representsMarginal_empty (L : Language (Fin d) K (Fin s)) (m : Operation (Fin d))
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) :
    RepresentsMarginal L m g le_rfl [] := by
  intro x
  simp only [ComplexityWeightedLayers.execute,List.foldl_nil,ComplexityWeightedLayers.finish,
    List.prod_nil,mul_one]
  rw [ComplexityCSPWordAssignment.assignmentWeight_tuple_eq L g hg,
    ComplexityCSPMarginalBounds.marginal_full]

/-- Prepending a valid class layer establishes the invariant one level lower,
including cancellation and zero-factor fallback cases. -/
theorem representsMarginal_prepend (L : Language (Fin d) K (Fin s))
    {m : Operation (Fin d)} (hm : IsMaltsev m) (g : ComplexityCSPCode.Code)
    {k : ℕ} (hk : k ≤ g.vertices) (hk1 : k+1 ≤ g.vertices)
    (layers : List (ComplexityWeightedLayers.Layer K)) (hrep : RepresentsMarginal L m g hk1 layers)
    (layer : Layer K d k)
    (hv : ValidLayer (ComplexityCSPMarginalBounds.marginal L g hk1) layer)
    (hclasses : ∀ a, Preserves m (rowFiber (ComplexityCSPMarginalBounds.marginal L g hk1) a)) :
    RepresentsMarginal L m g hk (encodeLayer layer :: layers) := by
  intro x
  rw [execute_prepend_layer, hrep]
  rw [← chooseRow_factor hm (ComplexityCSPMarginalBounds.marginal L g hk1) layer hv hclasses x]
  exact (ComplexityCSPMarginalBounds.marginal_succ L g hk hk1 (view x)).symm

omit [NeZero d] in
/-- The actual FP row-normalization callback has the exact literal marginal
row label whenever the constructed suffix invariant holds. -/
theorem label_of_representsMarginal [Algebra ℚ K] (L : Language (Fin d) K (Fin s))
    (m : Operation (Fin d)) (g : ComplexityCSPCode.Code) {k : ℕ} (hk1 : k+1 ≤ g.vertices)
    (layers : List (ComplexityWeightedLayers.Layer K)) (hrep : RepresentsMarginal L m g hk1 layers)
    (x : Tuple (Fin d) k) :
    ComplexityTypeRowCallback.label L (fun a b c => m (a,b,c)) (g,layers) (word x) =
      tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x) := by
  rw [ComplexityTypeRowCallback.label_tuple]
  have he := rowLabel_correct
    (fun y => ComplexityTypeRowCallback.evaluate L (fun a b c => m (a,b,c)) (g,layers) (word y))
    (ComplexityCSPMarginalBounds.marginal L g hk1) hrep
  exact congrFun he x

end PositiveDomain
end ComplexCSP.WeightedMaltsev
