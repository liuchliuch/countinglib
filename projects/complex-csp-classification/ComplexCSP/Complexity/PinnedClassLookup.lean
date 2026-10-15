import ComplexCSP.Complexity.PinnedClassExtension

/-! # Materialized class lookup from candidate words

A bounded list of actual candidate words is scanned in its literal order. Every
probe is the closed capped extension machine, including the eagerly evaluated
empty-anchor fallback branch.
-/
namespace ComplexCSP.ComplexityPinnedClass
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityProjectedClosure ComplexityWitnessPrimitives ComplexitySupportWitnessPrimitives ComplexityTypeStackMachines
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Fin d → Fin d → Fin d → Fin d) (space : Polynomial ℕ)

abbrev LookupInput (K : Type) (d : ℕ) := Input K d × (ℕ × ℕ)
noncomputable def lookupCode : BitEncoding (LookupInput K d) :=
  (inputCode basis).prod (BitEncoding.unaryNat.prod BitEncoding.nat)

noncomputable def probe (p : LookupInput K d × List ℕ) : MaybeWord :=
  extension L basis m space (p.1.1,p.1.2.1,p.1.2.2,p.2)

theorem fp_probe : FP ((lookupCode basis).prod wordCode) maybeCode (probe L basis m space) := by
  have hc := fp_fst (lookupCode (d:=d) basis) wordCode
  have hp := hc.comp (fp_fst (inputCode (d:=d) basis) (BitEncoding.unaryNat.prod BitEncoding.nat))
  have hia := hc.comp (fp_snd (inputCode (d:=d) basis) (BitEncoding.unaryNat.prod BitEncoding.nat))
  have hi := hia.comp (fp_fst BitEncoding.unaryNat BitEncoding.nat)
  have ha := hia.comp (fp_snd BitEncoding.unaryNat BitEncoding.nat)
  have hw := fp_snd (lookupCode (d:=d) basis) wordCode
  exact (hp.pair (hi.pair (ha.pair hw))).comp (fp_extension L basis m space)

noncomputable def accepts (p : LookupInput K d × List ℕ) : Bool :=
  !(decide (probe L basis m space p=[]))

theorem fp_accepts : FP ((lookupCode basis).prod wordCode) BitEncoding.bool (accepts L basis m space) :=
  ((fp_probe L basis m space).comp (ComplexitySupportWitnessPrimitives.fp_isEmpty wordCode)).comp
    (ArithmeticCircuitPrimitives.fp_bool_unary BitEncoding.bool not)

noncomputable def anchor (p : LookupInput K d × Rows) : MaybeWord :=
  first (p.2.filter (fun w => accepts L basis m space (p.1,w)))

theorem fp_anchor : FP ((lookupCode basis).prod rowsCode) maybeCode (anchor L basis m space) :=
  (ListContextFilterMachines.fp_filterWithContext (lookupCode basis) wordCode _
    (fp_accepts L basis m space)).comp fp_first

noncomputable def lookupFrom (p : LookupInput K d × Rows) : MaybeWord :=
  let z := anchor L basis m space p
  if z=[] then [] else probe L basis m space (p.1,z.headD [])

theorem fp_lookupFrom : FP ((lookupCode basis).prod rowsCode) maybeCode (lookupFrom L basis m space) := by
  let ei := (lookupCode (d:=d) basis).prod rowsCode
  have ha := fp_anchor L basis m space
  have he := ha.comp (ComplexitySupportWitnessPrimitives.fp_isEmpty wordCode)
  have hw := ha.comp (ListDecompositionMachines.fp_headD wordCode [])
  exact he.ite (fp_const ei maybeCode [])
    (((fp_fst (lookupCode basis) rowsCode).pair hw).comp (fp_probe L basis m space))

end ComplexCSP.ComplexityPinnedClass
