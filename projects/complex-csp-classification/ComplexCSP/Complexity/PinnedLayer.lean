import ComplexCSP.Complexity.PinnedClass

/-! # Actual raw buildPinnedLayer machine

The class labels are returned by the closed capped type-query machine. For each
literal returned label, the complete unary-pinned class witness is constructed
and serialized with its exact field factor. No label/constructor oracle occurs.
-/
namespace ComplexCSP.ComplexityPinnedLayer
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityWitnessEncoding ComplexitySupportWitnessPrimitives
open ComplexityTypeStackMachines MaltsevWitness WeightedMaltsev
open ComplexityPinnedClass
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Fin d → Fin d → Fin d → Fin d) (space : Polynomial ℕ) (defaultValue : Fin d)

omit [Algebra ℚ K] in
def projectContext (c : Context K d) : Context K d :=
  ⟨(c.val.1,c.val.2.1-1,projectWitness (c.val.2.1-1,c.val.2.2)),by
    obtain ⟨W,hW⟩ := c.property
    refine ⟨projectCode W (c.val.2.1-1) (Nat.sub_le _ _),?_⟩
    dsimp only
    rw [hW,projectWitness_encode]⟩

omit [DecidableEq K] in
theorem fp_projectContext : FP (ComplexityPinnedClass.contextCode (d:=d) basis)
    (ComplexityPinnedClass.contextCode basis) projectContext := by
  have hc := fp_contextView (d:=d) basis
  have hb := hc.comp (fp_fst (ComplexityTypeRowCallback.contextCode basis)
    (BitEncoding.unaryNat.prod witnessCode))
  have hw := (hc.comp (fp_snd (ComplexityTypeRowCallback.contextCode basis)
    (BitEncoding.unaryNat.prod witnessCode))).comp (fp_snd BitEncoding.unaryNat witnessCode)
  have ht := hw.comp (fp_fst tableCode maybeCode)
  have hk0 := (ht.comp (ListDecompositionMachines.fp_tail maybeCode.list [])).comp
    (ListUnaryLengthMachine.fp_length maybeCode.list)
  have hk : FP (ComplexityPinnedClass.contextCode (d:=d) basis) BitEncoding.unaryNat
      (fun c => c.val.2.1-1) := hk0.congr (by
    intro c
    obtain ⟨W,hW⟩ := c.property
    simp only [Function.comp_apply,List.length_tail]
    rw [hW,encodeCode_table_length])
  exact (hb.pair (hk.pair ((hk.pair hw).comp fp_projectWitness))).transportOutput (fun _ => rfl)

noncomputable def labels (c : Context K d) : List (RowLabel K d) :=
  (ComplexityTypeQuery.executeWithSpace L basis m space
    (c.val,0,List.replicate c.val.2.1 defaultValue.val)).1

theorem fp_labels : FP (ComplexityPinnedClass.contextCode basis)
    (ComplexityCSPMarginalRowBounds.labelEncoding basis d).list (labels L basis m space defaultValue) := by
  let ei := ComplexityPinnedClass.contextCode (d:=d) basis
  let e := ComplexityCSPMarginalRowBounds.labelEncoding basis d
  have hc := fp_contextView (d:=d) basis
  have hn := hc.comp (ComplexityTypeStackConcrete.fp_dimensionOf basis)
  have ht := (hn.pair (fp_const ei BitEncoding.nat defaultValue.val)).comp
    (RuntimePolynomialEvaluationMachines.fp_replicate BitEncoding.nat)
  have hq := (hc.pair ((fp_const ei BitEncoding.unaryNat 0).pair ht)).comp
    (ComplexityTypeQuery.fp_executeWithSpace L basis m space)
  exact hq.comp (fp_fst e.list (ComplexityTypeCache.cacheEncoding e))

noncomputable def classRecord (p : ShapedInput K d) : ComplexityWeightedLayers.ClassRecord K :=
  packClass (p.2,ComplexityPinnedClass.build L basis m space defaultValue p)

theorem fp_classRecord : FP (shapedInputCode basis) (ComplexityWeightedLayers.classCode basis)
    (classRecord L basis m space defaultValue) := by
  have hl := fp_snd (ComplexityPinnedClass.contextCode (d:=d) basis)
    (ComplexityCSPMarginalRowBounds.labelEncoding basis d)
  exact (hl.pair (ComplexityPinnedClass.fp_build L basis m space defaultValue)).comp (fp_packClass basis)

noncomputable def split (c : Context K d) : ComplexityWeightedLayers.Layer K :=
  (labels L basis m space defaultValue c).map (fun label => classRecord L basis m space defaultValue (c,label))

/-- Every enumerated label receives its independently constructed actual code. -/
theorem fp_split : FP (ComplexityPinnedClass.contextCode basis) (ComplexityWeightedLayers.layerCode basis)
    (split L basis m space defaultValue) :=
  (((fp_id (ComplexityPinnedClass.contextCode basis)).pair (fp_labels L basis m space defaultValue))).comp
    (ListContextMachines.fp_mapWithContext (ComplexityPinnedClass.contextCode basis)
      (ComplexityCSPMarginalRowBounds.labelEncoding basis d) (ComplexityWeightedLayers.classCode basis) _
      (fp_classRecord L basis m space defaultValue))

noncomputable def build (c : Context K d) : ComplexityWeightedLayers.Layer K :=
  split L basis m space defaultValue (projectContext c)

/-- Actual total raw layer constructor on shape-valid contexts, with no semantic
Correct, evaluator callback, type-label, BO, or constructor oracle hypothesis. -/
theorem fp_build : FP (ComplexityPinnedClass.contextCode basis) (ComplexityWeightedLayers.layerCode basis)
    (build L basis m space defaultValue) :=
  (fp_projectContext basis).comp (fp_split L basis m space defaultValue)

end ComplexCSP.ComplexityPinnedLayer
