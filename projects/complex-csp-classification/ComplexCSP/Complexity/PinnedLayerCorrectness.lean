import ComplexCSP.Complexity.PinnedLayerShape

/-! # Closed exact agreement with the typed pinned layer algorithm

The one chosen polynomial is the previously proved restricted marginal stack
bound. Every generic query agreement is discharged for the actual projected
support and for its actual unary coordinate pins. No constructor, label, query,
or output-size oracle is assumed.
-/
noncomputable section
namespace ComplexCSP.ComplexityPinnedLayer
open MaltsevWitness MaltsevRelations WeightedMaltsev ComplexityWitnessEncoding
open ComplexityWitnessPrimitives ComplexitySupportWitnessPrimitives ComplexityPinnedClass
open ComplexityLabelExtension
open PlanarHom PlanarHom.Complexity
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Operation (Fin d)) (defaultValue : Fin d)

/-- The actual closed compiler fixes its cap from the proved original-instance
marginal bound, rather than taking any evaluator/label construction as input. -/
def compile (c : Context K d) : ComplexityWeightedLayers.Layer K :=
  build L basis (curried m) (restrictedSpace L basis) defaultValue c

theorem fp_compile : FP (ComplexityPinnedClass.contextCode basis) (ComplexityWeightedLayers.layerCode basis)
    (compile L basis m defaultValue) := fp_build L basis (curried m) (restrictedSpace L basis) defaultValue

theorem compile_shape (c : Context K d) : ∃ layer : WeightedMaltsev.Layer K d (c.val.2.1-1),
    compile L basis m defaultValue c=encodeLayer layer :=
  build_shape L basis m (restrictedSpace L basis) defaultValue c

variable (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
variable (k : ℕ) (hk1 : k+1≤g.vertices) (hm : IsMaltsev m)
variable (σ : K →+* ℂ)
variable (hBO : BlockOrthogonality.BlockOrthogonal
  (fun x a => σ (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) x a)))
variable (layers : List (ComplexityWeightedLayers.Layer K))
variable (hrep : RepresentsMarginal L m g hk1 layers)

include hg hm hBO hrep in
theorem extensionAgrees_marginal (R : Set (Fin k → Fin d))
    (hsub : R⊆rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1))
    (W : Code (Fin d) k) (hW : Correct W R) (hR : Preserves m R)
    (hTP : TypesPartition R (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x))) :
    ExtensionAgrees L basis m (restrictedSpace L basis) (g,layers) W
      (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)) := by
  intro wanted fuel len hdepth target
  rw [packContext_store]
  simpa only [restrictedQuery,storeCode_toCode] using restrictedQuery_correct L basis g hg k hk1 R hsub m hm (storeCode W)
    (by simpa using hW) hR hTP σ hBO layers hrep wanted fuel len hdepth target

include hg hm hBO hrep in
theorem split_marginal_eq (W : Code (Fin d) k)
    (hW : Correct W (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1)))
    (hEq : PreservesRowEquivalence m (rowFiber (ComplexityCSPMarginalBounds.marginal L g hk1))) :
    split L basis (curried m) (restrictedSpace L basis) defaultValue (packContext (g,layers) W)=
      encodeLayer (splitPinnedTypeClasses m W
        (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)) defaultValue) := by
  let G := ComplexityCSPMarginalBounds.marginal L g hk1
  let label := fun x : Tuple (Fin d) k => tableLabel G (view x)
  have hEq' : PreservesRowEquivalence m (labelFiber (rowSupport G) label) := by
    rw [show labelFiber (rowSupport G) label=rowFiber G from labelFiber_rowFiber G]
    exact hEq
  have hR := row_equivalence_support_preserves hEq'
  have hTP := (allTypesPartition_of_row_equivalence hm hEq').base
  have hext := extensionAgrees_marginal L basis m g hg k hk1 hm σ hBO layers hrep
    (rowSupport G) (fun _ h => h) W hW hR hTP
  have hpins : ∀ (i : Fin k) (a : Fin d), ExtensionAgrees L basis m (restrictedSpace L basis)
      (g,layers) (coordinatePinCode m W i a).toCode label := by
    intro i a
    exact extensionAgrees_marginal L basis m g hg k hk1 hm σ hBO layers hrep
      (coordinatePin (rowSupport G) i a) (fun _ h => h.1) (coordinatePinCode m W i a).toCode
      (coordinatePinCode_correct hm hR hW i a) (coordinatePin_preserves hm hR i a)
      (coordinatePin_typesPartition hm hEq' i a)
  have hlabels : labels L basis (curried m) (restrictedSpace L basis) defaultValue (packContext (g,layers) W)=
      (materializedTypeSearch m W label k 0 (Vector.ofFn (fun _ => defaultValue)) []).1 := by
    unfold labels
    have ht : List.replicate k defaultValue.val=word (Vector.ofFn (fun _ : Fin k => defaultValue)) := by
      simp [word,Vector.toList_ofFn,List.ofFn_const]
    change (ComplexityTypeQuery.executeWithSpace L basis (curried m) (restrictedSpace L basis)
      ((packContext (g,layers) W).val,0,List.replicate k defaultValue.val)).1=_
    rw [ht,packContext_store]
    simpa only [storeCode_toCode,label,G] using congrArg Prod.fst (restrictedTypeQuery_correct L basis g hg k hk1 (rowSupport G)
      (fun _ h => h) m hm (storeCode W) (by simpa using hW) hR hTP σ hBO layers hrep
      k 0 (by omega) (Vector.ofFn (fun _ => defaultValue)))
  unfold split
  rw [hlabels]
  simp only [encodeLayer,splitPinnedTypeClasses,List.map_map]
  apply List.map_congr_left
  intro a _
  unfold classRecord
  rw [ComplexityPinnedClass.build_eq L basis m (restrictedSpace L basis) defaultValue
    (g,layers) W label hext hpins]
  simp only [Function.comp_apply,packClass,encodeClass,encodeCode_store,storeCode,label,G]

include hg hm hBO hrep in
/-- Full literal agreement, including chosen seeds/lookups, label ordering,
zero-dimensional rows, and exact normalized factors. -/
theorem compile_eq_buildPinnedLayer (W : Code (Fin d) (k+1))
    (hW : Correct W {x | ComplexityCSPMarginalBounds.marginal L g hk1 x≠0})
    (hEq : PreservesRowEquivalence m (rowFiber (ComplexityCSPMarginalBounds.marginal L g hk1))) :
    compile L basis m defaultValue (packContext (g,layers) W)=
      encodeLayer (buildPinnedLayer m W
        (fun x => ComplexityTypeRowCallback.evaluate L (curried m) (g,layers) (word x)) defaultValue) := by
  have hproj : projectContext (packContext (g,layers) W)=
      packContext (g,layers) (projectCode W k (Nat.le_succ k)) := by
    apply Subtype.ext
    simp only [projectContext,packContext,Nat.add_sub_cancel]
    rw [projectWitness_encode W (Nat.le_succ k)]
  unfold compile build
  rw [hproj]
  have hP : Correct (projectCode W k (Nat.le_succ k))
      (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1)) := by
    simpa only [projection_rowSupport] using projectCode_correct hW k (Nat.le_succ k)
  have he : rowLabel (fun x => ComplexityTypeRowCallback.evaluate L (curried m) (g,layers) (word x))=
      (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)) :=
    rowLabel_correct _ _ hrep
  rw [buildPinnedLayer,he]
  exact split_marginal_eq L basis m defaultValue g hg k hk1 hm σ hBO layers hrep
    (projectCode W k (Nat.le_succ k)) hP hEq

end ComplexCSP.ComplexityPinnedLayer
