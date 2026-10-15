import ComplexCSP.Complexity.SupportInitialSemantics
import ComplexCSP.Complexity.PinnedOuterMachine

/-! # One actual initial-support / outer-loop / final-product evaluator

This is the complete bit-program composition. Runtime is proved on every raw
CSP code; the subsequent correctness theorem restricts only the intended valid
ordinary or divisible-degree source promise. No evaluator, representation or
constructor program is supplied as a hypothesis.
-/
namespace ComplexCSP.ComplexityPinnedEvaluator
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityWitnessEncoding ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations WeightedMaltsev
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Operation (Fin d)) (defaultValue : Fin d)

noncomputable def startContext (g : ComplexityCSPCode.Code) : ComplexityPinnedClass.Context K d :=
  ⟨((g,[]),g.vertices,rawSupportCompiler L (ComplexityLabelExtension.curried m) defaultValue g),
    rawSupportCompiler_shape L (ComplexityLabelExtension.curried m) defaultValue g⟩

theorem fp_startContext : FP ComplexityCSPCode.encoding (ComplexityPinnedClass.contextCode basis)
    (startContext L m defaultValue) := by
  have hv : FP ComplexityCSPCode.encoding
      (BitEncoding.unaryNat.prod ComplexityCSPCode.constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hn := hv.comp (fp_fst BitEncoding.unaryNat ComplexityCSPCode.constraintEncoding.list)
  have hb := (fp_id ComplexityCSPCode.encoding).pair
    (fp_const ComplexityCSPCode.encoding (ComplexityWeightedLayers.layerCode basis).list [])
  have hw := fp_rawSupportCompiler L (ComplexityLabelExtension.curried m) defaultValue
  exact (hb.pair (hn.pair hw)).transportOutput (fun _ => rfl)

omit [Algebra ℚ K] in
/-- Literal initialization agreement; all zero-variable conventions are already
proved by the actual support compiler. -/
theorem startContext_eq (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) :
    startContext L m defaultValue g =
      ComplexityPinnedClass.packContext (g,[]) (rawSupportWitness L m defaultValue g hg).toCode := by
  apply Subtype.ext
  simp only [startContext,ComplexityPinnedClass.packContext]
  rw [rawSupportCompiler_encode L m defaultValue g hg]

noncomputable def run (querySpace outerSpace : Polynomial ℕ) (g : ComplexityCSPCode.Code) : K :=
  ComplexityPinnedOuter.evaluate L basis m querySpace defaultValue outerSpace (startContext L m defaultValue g)

/-- Full finite-control polynomial-time program, on all raw codes. Chosen fixed
polynomial constants do not receive an oracle interpretation at runtime. -/
theorem fp_run (querySpace outerSpace : Polynomial ℕ) :
    FP ComplexityCSPCode.encoding (numberFieldEncoding basis) (run L basis m defaultValue querySpace outerSpace) :=
  (fp_startContext L basis m defaultValue).comp
    (ComplexityPinnedOuter.fp_evaluate L basis m querySpace defaultValue outerSpace)

end ComplexCSP.ComplexityPinnedEvaluator
