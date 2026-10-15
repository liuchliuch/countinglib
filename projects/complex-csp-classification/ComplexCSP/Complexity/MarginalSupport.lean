import ComplexCSP.Complexity.WitnessUnionSemantics
import ComplexCSP.Structure.WeightedMaltsevMachineBridge
import ComplexCSP.Complexity.EncodedEquality

/-! # Actual FP marginal-support update from nonzero class factors

Zero-sum classes are removed by canonical field equality before the concrete
union-witness compiler runs. Empty retained lists and zero-dimensional witnesses
use the same total machine and preserve missing/present-empty distinctions.
-/
namespace ComplexCSP.ComplexityMarginalSupport
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityWitnessEncoding ComplexitySupportWitnessPrimitives
open WeightedMaltsev MaltsevWitness MaltsevRelations
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension n : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K) (m : Fin d → Fin d → Fin d → Fin d)

def retainedWitnesses (layer : ComplexityWeightedLayers.Layer K) : List RawWitness :=
  (layer.filter (fun e => decide (e.2.1 ≠ 0))).map (fun e => e.2.2)

theorem fp_retainedWitnesses : FP (ComplexityWeightedLayers.layerCode basis)
    ComplexityWitnessUnion.familyCode (retainedWitnesses : ComplexityWeightedLayers.Layer K → _) := by
  let ec := ComplexityWeightedLayers.classCode basis
  let ek := numberFieldEncoding basis
  have hrest := fp_snd BitEncoding.nat (ek.prod witnessCode)
  have hfactor := hrest.comp (fp_fst ek witnessCode)
  have hz := (hfactor.pair (fp_const ec ek 0)).comp (ComplexityEncodedEquality.fp_equal ek)
  have ht := hz.ite (fp_const ec BitEncoding.bool false) (fp_const ec BitEncoding.bool true)
  have ht' : FP ec BitEncoding.bool (fun e : ComplexityWeightedLayers.ClassRecord K => decide (e.2.1 ≠ 0)) :=
    ht.congr (fun e => by simp)
  have hf := ListFilterMachines.fp_filter ec _ ht'
  exact hf.comp (ListMapMachines.fp_map ec witnessCode (fun e => e.2.2)
    (hrest.comp (fp_snd ek witnessCode)))

def build (p : ℕ × ComplexityWeightedLayers.Layer K) : RawWitness :=
  ComplexityWitnessUnion.build m (p.1,retainedWitnesses p.2)

theorem fp_build : FP (BitEncoding.unaryNat.prod (ComplexityWeightedLayers.layerCode basis))
    witnessCode (build m) :=
  ((fp_fst BitEncoding.unaryNat (ComplexityWeightedLayers.layerCode basis)).pair
    ((fp_snd BitEncoding.unaryNat (ComplexityWeightedLayers.layerCode basis)).comp
      (fp_retainedWitnesses basis))).comp (ComplexityWitnessUnion.fp_build m)

omit [Algebra ℚ K] in
theorem retainedWitnesses_encode (layer : Layer K d n) :
    retainedWitnesses (encodeLayer layer) = (retainedClasses layer).map (fun e => encodeCode e.2.toCode) := by
  simp only [retainedWitnesses,encodeLayer,List.filter_map,List.map_map,Function.comp_def,
    encodeClass,retainedClasses]
  simp_rw [encodeCode_stored]
  rfl

omit [Algebra ℚ K] in
/-- Exact stored-code equality; no correctness hypothesis is needed merely to
identify the materialized table and seed produced by the machine. -/
theorem build_encode (operation : Operation (Fin d)) (layer : Layer K d n) :
    build (fun a b c => operation (a,b,c)) (n,encodeLayer layer) =
      (rawTable (marginalSupportCode operation layer),maybeWord (marginalSupportCode operation layer).seed) := by
  rw [build,retainedWitnesses_encode,ComplexityWitnessUnion.build_encode]
  exact encodeCode_store _

end ComplexCSP.ComplexityMarginalSupport
