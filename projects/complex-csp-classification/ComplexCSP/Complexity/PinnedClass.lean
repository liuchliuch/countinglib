import ComplexCSP.Complexity.PinnedClassLookup
import ComplexCSP.Complexity.PinnedClassContext

/-! # Actual unary-pinned class witness compiler

A context carries a constructor-produced finite-domain witness shape, with its
literal dimension. The restriction changes no input bits. It imposes no support,
Correct, Maltsev, or type-partition assumption on the FP theorem. Unary probes
use the explicit positive fallback before restricted support submachines.
-/
namespace ComplexCSP.ComplexityPinnedClass
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityWitnessEncoding ComplexitySupportWitnessPrimitives
open ComplexityTypeStackMachines ComplexityProjectedClosure MaltsevWitness WeightedMaltsev
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Fin d → Fin d → Fin d → Fin d) (space : Polynomial ℕ) (defaultValue : Fin d)

abbrev ShapedInput (K : Type) (d : ℕ) := Context K d × RowLabel K d
noncomputable def shapedInputCode : BitEncoding (ShapedInput K d) :=
  (contextCode basis).prod (ComplexityCSPMarginalRowBounds.labelEncoding basis d)

def inputView (p : ShapedInput K d) : Input K d := (p.1.val,p.2)
omit [DecidableEq K] in
theorem fp_inputView : FP (shapedInputCode (d:=d) basis) (inputCode basis) inputView :=
  fp_code_view _ _ _ (fun _ => rfl)

/-- The pin only changes witness data; the marginal row callback is unchanged. -/
def pinnedInput (a : Fin d) (p : ShapedInput K d × ℕ) : Input K d :=
  ((p.1.1.val.1,p.1.1.val.2.1,
      (unaryPin defaultValue m a (contextWitness p.1.1,p.2)).val),p.1.2)

theorem fp_pinnedInput (a : Fin d) :
    FP ((shapedInputCode basis).prod BitEncoding.unaryNat) (inputCode basis)
      (pinnedInput m defaultValue a) := by
  let ei := (shapedInputCode (d:=d) basis).prod BitEncoding.unaryNat
  have hp := fp_fst (shapedInputCode (d:=d) basis) BitEncoding.unaryNat
  have hi := (fp_snd (shapedInputCode (d:=d) basis) BitEncoding.unaryNat).comp
    UnaryNatConversionMachine.fp_conversion
  have hc := hp.comp (fp_fst (contextCode (d:=d) basis)
    (ComplexityCSPMarginalRowBounds.labelEncoding basis d))
  have hraw := hc.comp (fp_contextView basis)
  have hbase := hraw.comp (fp_fst (ComplexityTypeRowCallback.contextCode basis)
    (BitEncoding.unaryNat.prod witnessCode))
  have hn := hraw.comp (ComplexityTypeStackConcrete.fp_dimensionOf basis)
  have hw := ((hc.comp (fp_contextWitness basis)).pair hi).comp (fp_unaryPin_raw defaultValue m a)
  have hl := hp.comp (fp_snd (contextCode (d:=d) basis)
    (ComplexityCSPMarginalRowBounds.labelEncoding basis d))
  exact (hbase.pair (hn.pair hw)).pair hl

noncomputable def coordinateWitness (a : Fin d) (p : ShapedInput K d × ℕ) : MaybeWord :=
  seed L basis m space a (pinnedInput m defaultValue a p)

theorem fp_coordinateWitness (a : Fin d) :
    FP ((shapedInputCode basis).prod BitEncoding.unaryNat) maybeCode
      (coordinateWitness L basis m space defaultValue a) :=
  (fp_pinnedInput basis m defaultValue a).comp (fp_seed L basis m space a)

noncomputable def candidates (p : ShapedInput K d × ℕ) : Rows :=
  (List.finRange d).flatMap (fun a => coordinateWitness L basis m space defaultValue a p)

theorem fp_candidates : FP ((shapedInputCode basis).prod BitEncoding.unaryNat) rowsCode
    (candidates L basis m space defaultValue) := by
  have h := ComplexityPinnedLayer.fp_fixedList ((shapedInputCode (d:=d) basis).prod BitEncoding.unaryNat)
    maybeCode (List.finRange d) (fun p a => coordinateWitness L basis m space defaultValue a p)
    (fun a _ => fp_coordinateWitness L basis m space defaultValue a)
  exact (h.comp (ListFlattenMachines.fp_flatten wordCode)).congr
    (fun _ => List.flatMap_def.symm)

noncomputable def lookup (p : ShapedInput K d × (ℕ × ℕ)) : MaybeWord :=
  lookupFrom L basis m space ((inputView p.1,p.2),candidates L basis m space defaultValue (p.1,p.2.1))

theorem fp_lookup : FP ((shapedInputCode basis).prod (BitEncoding.unaryNat.prod BitEncoding.nat))
    maybeCode (lookup L basis m space defaultValue) := by
  have hp := fp_fst (shapedInputCode (d:=d) basis) (BitEncoding.unaryNat.prod BitEncoding.nat)
  have hia := fp_snd (shapedInputCode (d:=d) basis) (BitEncoding.unaryNat.prod BitEncoding.nat)
  have hi := hia.comp (fp_fst BitEncoding.unaryNat BitEncoding.nat)
  have hc := (hp.pair hi).comp (fp_candidates L basis m space defaultValue)
  exact (((hp.comp (fp_inputView basis)).pair hia).pair hc).comp (fp_lookupFrom L basis m space)

noncomputable def build (p : ShapedInput K d) : RawWitness :=
  ((List.range p.1.val.2.1).map (fun i => (List.finRange d).map
      (fun a => lookup L basis m space defaultValue (p,i,a.val))),
    seed L basis m space defaultValue (inputView p))

/-- Complete n*d table materialization by actual finite-list machines. -/
theorem fp_build : FP (shapedInputCode basis) witnessCode (build L basis m space defaultValue) := by
  let ei := shapedInputCode (d:=d) basis
  let ec := ei.prod BitEncoding.unaryNat
  have hp := fp_fst ei BitEncoding.unaryNat
  have hi := fp_snd ei BitEncoding.unaryNat
  have hrow := ComplexityPinnedLayer.fp_fixedList ec maybeCode (List.finRange d)
    (fun p a => lookup L basis m space defaultValue (p.1,p.2,a.val)) (by
      intro a _
      exact (hp.pair (hi.pair (fp_const ec BitEncoding.nat a.val))).comp
        (fp_lookup L basis m space defaultValue))
  have hn := (((fp_fst (contextCode (d:=d) basis)
    (ComplexityCSPMarginalRowBounds.labelEncoding basis d)).comp (fp_contextView basis))).comp
      (ComplexityTypeStackConcrete.fp_dimensionOf basis)
  have his := hn.comp ComplexityPinnedLayer.fp_unaryRange
  have htable := ((fp_id ei).pair his).comp
    (ListContextMachines.fp_mapWithContext ei BitEncoding.unaryNat maybeCode.list _ hrow)
  exact htable.pair ((fp_inputView basis).comp (fp_seed L basis m space defaultValue))

end ComplexCSP.ComplexityPinnedClass
