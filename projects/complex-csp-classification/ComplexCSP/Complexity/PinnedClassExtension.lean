import ComplexCSP.Complexity.PinnedClassIndices
import ComplexCSP.Complexity.LabelExtensionBounds

/-! # Concrete class seed and prefix-extension subprograms

The original instance and completed weighted layers stay in the immutable
context. Calls use the actual capped query/greedy extension machine, and every
raw branch is safe even for empty words or out-of-range coordinates.
-/
namespace ComplexCSP.ComplexityPinnedClass
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityWitnessEncoding ComplexitySupportWitnessPrimitives
open ComplexityTypeStackMachines MaltsevWitness WeightedMaltsev MaltsevTypeStack
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Fin d → Fin d → Fin d → Fin d) (space : Polynomial ℕ)

abbrev Input (K : Type) (d : ℕ) := ComplexityTypeStackConcrete.Context K × RowLabel K d
noncomputable def inputCode : BitEncoding (Input K d) :=
  (ComplexityTypeStackConcrete.contextCode basis).prod
    (ComplexityCSPMarginalRowBounds.labelEncoding basis d)

/-- Option words and their zero-or-one-element lists have identical codes. -/
theorem fp_optionList : FP (optionCode wordCode) maybeCode (Option.toList : Option (List ℕ) → _) :=
  fp_code_view _ _ _ (fun _ => rfl)

noncomputable def seed (a : Fin d) (p : Input K d) : MaybeWord :=
  (ComplexityLabelExtension.extendQuery L basis m space
    (p.1,p.2,0,List.replicate p.1.2.1 a.val)).toList

theorem fp_seed (a : Fin d) : FP (inputCode (d:=d) basis) maybeCode (seed L basis m space a) := by
  let ec := ComplexityTypeStackConcrete.contextCode basis
  let e := ComplexityCSPMarginalRowBounds.labelEncoding basis d
  have hc := fp_fst ec e
  have hl := fp_snd ec e
  have hn := hc.comp (ComplexityTypeStackConcrete.fp_dimensionOf basis)
  have ht := (hn.pair (fp_const (inputCode (d:=d) basis) BitEncoding.nat a.val)).comp
    (RuntimePolynomialEvaluationMachines.fp_replicate BitEncoding.nat)
  exact ((hc.pair (hl.pair ((fp_const (inputCode (d:=d) basis) BitEncoding.unaryNat 0).pair ht))).comp
    (ComplexityLabelExtension.fp_query L basis m space)).comp fp_optionList

abbrev ExtensionInput (K : Type) (d : ℕ) := Input K d × (ℕ × (ℕ × List ℕ))
noncomputable def extensionCode : BitEncoding (ExtensionInput K d) :=
  (inputCode (d:=d) basis).prod (BitEncoding.unaryNat.prod (BitEncoding.nat.prod wordCode))

noncomputable def extension (p : ExtensionInput K d) : MaybeWord :=
  (ComplexityLabelExtension.extendQuery L basis m space
    (p.1.1,p.1.2,p.2.1+1,replaceAt p.2.2.2 p.2.1 p.2.2.1)).toList

theorem fp_extension : FP (extensionCode basis) maybeCode (extension L basis m space) := by
  let ei := extensionCode (d:=d) basis
  let tail := BitEncoding.unaryNat.prod (BitEncoding.nat.prod wordCode)
  have hp := fp_fst (inputCode (d:=d) basis) tail
  have hc := hp.comp (fp_fst (ComplexityTypeStackConcrete.contextCode basis)
    (ComplexityCSPMarginalRowBounds.labelEncoding basis d))
  have hl := hp.comp (fp_snd (ComplexityTypeStackConcrete.contextCode basis)
    (ComplexityCSPMarginalRowBounds.labelEncoding basis d))
  have hargs := fp_snd (inputCode (d:=d) basis) tail
  have hi := hargs.comp (fp_fst BitEncoding.unaryNat (BitEncoding.nat.prod wordCode))
  have haw := hargs.comp (fp_snd BitEncoding.unaryNat (BitEncoding.nat.prod wordCode))
  have ha := haw.comp (fp_fst BitEncoding.nat wordCode)
  have hw := haw.comp (fp_snd BitEncoding.nat wordCode)
  have ht := (((hi.comp UnaryNatConversionMachine.fp_conversion).pair ha).pair hw).comp fp_replaceAt
  exact ((hc.pair (hl.pair ((hi.comp fp_unarySucc).pair ht))).comp
    (ComplexityLabelExtension.fp_query L basis m space)).comp fp_optionList

end ComplexCSP.ComplexityPinnedClass
