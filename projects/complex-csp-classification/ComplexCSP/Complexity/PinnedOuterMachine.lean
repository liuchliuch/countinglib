import ComplexCSP.Complexity.PinnedOuterFrame
import ComplexCSP.Complexity.PinnedLayerShape
import ComplexCSP.Complexity.CappedIteration

/-! # Closed capped machine for the complete pinned outer iteration

Each raw step runs the actual layer and marginal-support constructors. Shape
proofs are only finite table/tuple representation facts. Dimension zero freezes
the state. Every intermediate is capped by a literal unary budget computed
from input length; semantic proofs separately show no genuine run is capped.
-/
namespace ComplexCSP.ComplexityPinnedOuter
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityWitnessEncoding ComplexitySupportWitnessPrimitives
open ComplexityTypeStackMachines MaltsevWitness MaltsevRelations WeightedMaltsev
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Operation (Fin d)) (querySpace : Polynomial ℕ) (defaultValue : Fin d)

noncomputable def advance (c : ComplexityPinnedClass.Context K d) : ComplexityPinnedClass.Context K d :=
  if c.val.2.1=0 then c else
    ⟨update (ComplexityLabelExtension.curried m)
      (c.val,ComplexityPinnedLayer.build L basis (ComplexityLabelExtension.curried m) querySpace defaultValue c),
      update_shaped m c.val _ (ComplexityPinnedLayer.build_shape L basis m querySpace defaultValue c)⟩

/-- Actual total step compiler with all constructor FP premises discharged. -/
theorem fp_advance : FP (ComplexityPinnedClass.contextCode basis) (ComplexityPinnedClass.contextCode basis)
    (advance L basis m querySpace defaultValue) := by
  let es := ComplexityPinnedClass.contextCode (d:=d) basis
  let er := ComplexityTypeStackConcrete.contextCode basis
  have hc := ComplexityPinnedClass.fp_contextView (d:=d) basis
  have hn := (hc.comp (ComplexityTypeStackConcrete.fp_dimensionOf basis)).comp
    UnaryNatConversionMachine.fp_conversion
  have hz := (hn.pair (fp_const es BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  have hu := (hc.pair (ComplexityPinnedLayer.fp_build L basis
    (ComplexityLabelExtension.curried m) querySpace defaultValue)).comp
      (fp_update basis (ComplexityLabelExtension.curried m))
  have hr := hz.ite hc hu
  apply hr.transportOutput
  intro c
  by_cases h : c.val.2.1=0 <;>
    simp [advance,h,Function.comp_def,ComplexityTypeStackConcrete.dimensionOf,
      ComplexityPinnedClass.contextCode,BitEncoding.restrict]

@[simp] theorem advance_zero (c : ComplexityPinnedClass.Context K d) (hc : c.val.2.1=0) :
    advance L basis m querySpace defaultValue c = c := by simp [advance,hc]

noncomputable def transition (p : ℕ × ComplexityPinnedClass.Context K d) : Option (ComplexityPinnedClass.Context K d) :=
  some (advance L basis m querySpace defaultValue p.2)

theorem fp_transition : FP (BitEncoding.nat.prod (ComplexityPinnedClass.contextCode basis))
    (optionCode (ComplexityPinnedClass.contextCode basis)) (transition L basis m querySpace defaultValue) :=
  ((fp_snd BitEncoding.nat (ComplexityPinnedClass.contextCode basis)).comp
    (fp_advance L basis m querySpace defaultValue)).comp (fp_some (ComplexityPinnedClass.contextCode basis))

noncomputable def execute (outerSpace : Polynomial ℕ) (c : ComplexityPinnedClass.Context K d) :
    ComplexityPinnedClass.Context K d :=
  ComplexityCappedIteration.runWithBudgets BitEncoding.nat (ComplexityPinnedClass.contextCode basis)
    (ComplexityPinnedClass.fallback ⟨0,[]⟩)
    (transition L basis m querySpace defaultValue) outerSpace Polynomial.X (0,c)

/-- Closed FP outer loop, valid on every shape-coded input regardless of
correctness, actual support, block orthogonality or success of internal caps. -/
theorem fp_execute (outerSpace : Polynomial ℕ) :
    FP (ComplexityPinnedClass.contextCode basis) (ComplexityPinnedClass.contextCode basis)
      (execute L basis m querySpace defaultValue outerSpace) := by
  let es := ComplexityPinnedClass.contextCode (d:=d) basis
  have h := ComplexityCappedIteration.fp_runWithBudgets BitEncoding.nat es
    (ComplexityPinnedClass.fallback (K:=K) (d:=d) ⟨0,[]⟩)
    (transition L basis m querySpace defaultValue) (fp_transition L basis m querySpace defaultValue)
    outerSpace Polynomial.X
  exact ((fp_const es BitEncoding.nat 0).pair (fp_id es)).comp h

/-- No-cap theorem for the literal actual outer step. The required cap bound
will be supplied by the original-instance reached-context invariant. -/
theorem execute_eq_iterate (outerSpace : Polynomial ℕ) (c : ComplexityPinnedClass.Context K d)
    (hbound : ∀ i, i ≤ ((BitEncoding.nat.prod (ComplexityPinnedClass.contextCode basis)).encode (0,c)).length →
      ((ComplexityPinnedClass.contextCode basis).encode
        ((advance L basis m querySpace defaultValue)^[i] c)).length ≤
      outerSpace.eval ((BitEncoding.nat.prod (ComplexityPinnedClass.contextCode basis)).encode (0,c)).length) :
    execute L basis m querySpace defaultValue outerSpace c =
      (advance L basis m querySpace defaultValue)^[((BitEncoding.nat.prod
        (ComplexityPinnedClass.contextCode basis)).encode (0,c)).length] c := by
  have h := ComplexityCappedIteration.runWithBudgets_correct BitEncoding.nat
    (ComplexityPinnedClass.contextCode basis) (ComplexityPinnedClass.fallback (K:=K) (d:=d) ⟨0,[]⟩)
    (transition L basis m querySpace defaultValue) outerSpace Polynomial.X (0,c)
    (by simpa only [Polynomial.eval_X,ComplexityCappedIteration.next,transition,Option.getD_some] using hbound)
  simpa only [execute,Polynomial.eval_X,ComplexityCappedIteration.next,transition,Option.getD_some] using h


/-- Final actual ComputeF call on the stored original instance and layers. -/
def finish (c : ComplexityPinnedClass.Context K d) : K :=
  ComplexityWeightedLayers.execute (ComplexityLabelExtension.curried m) L c.val.1.1 [] c.val.1.2

theorem fp_finish : FP (ComplexityPinnedClass.contextCode basis) (numberFieldEncoding basis) (finish L m) := by
  let el := ComplexityWeightedLayers.layerCode basis
  have hb := (ComplexityPinnedClass.fp_contextView (d:=d) basis).comp
    (fp_fst (ComplexityTypeRowCallback.contextCode basis) (BitEncoding.unaryNat.prod witnessCode))
  have hg := hb.comp (fp_fst ComplexityCSPCode.encoding el.list)
  have hl := hb.comp (fp_snd ComplexityCSPCode.encoding el.list)
  exact (hg.pair ((fp_const (ComplexityPinnedClass.contextCode (d:=d) basis) wordCode []).pair hl)).comp
    (ComplexityWeightedLayers.fp_execute basis (ComplexityLabelExtension.curried m) L)

noncomputable def evaluate (outerSpace : Polynomial ℕ) (c : ComplexityPinnedClass.Context K d) : K :=
  finish L m (execute L basis m querySpace defaultValue outerSpace c)

theorem fp_evaluate (outerSpace : Polynomial ℕ) :
    FP (ComplexityPinnedClass.contextCode basis) (numberFieldEncoding basis)
      (evaluate L basis m querySpace defaultValue outerSpace) :=
  (fp_execute L basis m querySpace defaultValue outerSpace).comp (fp_finish L basis m)

end ComplexCSP.ComplexityPinnedOuter
