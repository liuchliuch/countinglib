import ComplexCSP.Complexity.TypeQuery
import ComplexCSP.Complexity.EncodedEquality

/-! # Actual raw greedy extension with closed capped type queries

Every candidate color is tested by the total capped type-query machine. All
branches, including inactive/malformed states, therefore have genuine FP
implementations even under eager conditional evaluation.
-/
namespace ComplexCSP.ComplexityLabelExtension
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityTypeStackMachines MaltsevTypeStack
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Fin d → Fin d → Fin d → Fin d) (space : Polynomial ℕ)

abbrev State (K : Type) (d : ℕ) :=
  (ComplexityTypeStackConcrete.Context K × WeightedMaltsev.RowLabel K d) × (ℕ × (List ℕ × Bool))
noncomputable def stateCode : BitEncoding (State K d) :=
  ((ComplexityTypeStackConcrete.contextCode basis).prod (ComplexityCSPMarginalRowBounds.labelEncoding basis d)).prod
    (BitEncoding.unaryNat.prod (wordCode.prod BitEncoding.bool))

def context (p : State K d) := p.1.1
def wanted (p : State K d) := p.1.2
def len (p : State K d) := p.2.1
def target (p : State K d) := p.2.2.1
def alive (p : State K d) := p.2.2.2

noncomputable def accepts (p : State K d) (a : ℕ) : Bool :=
  decide (wanted p ∈ (ComplexityTypeQuery.executeWithSpace L basis m space
    (context p,len p+1,replaceAt (target p) (len p) a)).1)
noncomputable def candidates (p : State K d) : List ℕ := (List.range d).filter (accepts L basis m space p)
noncomputable def choose (p : State K d) : Option ℕ := (candidates L basis m space p).head?

noncomputable def step (p : State K d) : State K d :=
  if alive p then
    if len p < ComplexityTypeStackConcrete.dimensionOf (context p) then
      match choose L basis m space p with
      | none => (p.1,len p,target p,false)
      | some a => (p.1,len p+1,replaceAt (target p) (len p) a,true)
    else p
  else p

noncomputable def finish (p : State K d) : Option (List ℕ) :=
  if alive p then
    (ComplexityTypeStackConcrete.reconstruct m (context p,len p,target p)).filter
      (fun w => decide (ComplexityTypeStackConcrete.rowLabelOf L m (context p,w)=wanted p))
  else none

omit [DecidableEq K] in
theorem fp_context : FP (stateCode (d:=d) basis) (ComplexityTypeStackConcrete.contextCode basis) context :=
  (fp_fst _ _).comp (fp_fst _ _)
omit [DecidableEq K] in
theorem fp_wanted : FP (stateCode (d:=d) basis) (ComplexityCSPMarginalRowBounds.labelEncoding basis d) wanted :=
  (fp_fst _ _).comp (fp_snd _ _)
omit [DecidableEq K] in
theorem fp_len : FP (stateCode (d:=d) basis) BitEncoding.unaryNat len :=
  (fp_snd _ _).comp (fp_fst _ _)
omit [DecidableEq K] in
theorem fp_target : FP (stateCode (d:=d) basis) wordCode target :=
  ((fp_snd _ _).comp (fp_snd _ _)).comp (fp_fst _ _)
omit [DecidableEq K] in
theorem fp_alive : FP (stateCode (d:=d) basis) BitEncoding.bool alive :=
  ((fp_snd _ _).comp (fp_snd _ _)).comp (fp_snd _ _)

theorem fp_accepts : FP ((stateCode (d:=d) basis).prod BitEncoding.nat) BitEncoding.bool
    (fun p => accepts L basis m space p.1 p.2) := by
  let ei := (stateCode (d:=d) basis).prod BitEncoding.nat
  let e := ComplexityCSPMarginalRowBounds.labelEncoding basis d
  have hp := fp_fst (stateCode (d:=d) basis) BitEncoding.nat
  have ha := fp_snd (stateCode (d:=d) basis) BitEncoding.nat
  have hc := hp.comp (fp_context basis)
  have hw := hp.comp (fp_wanted basis)
  have hn := hp.comp (fp_len basis)
  have ht := hp.comp (fp_target basis)
  have hr := (((hn.comp UnaryNatConversionMachine.fp_conversion).pair ha).pair ht).comp fp_replaceAt
  have hq := (hc.pair ((hn.comp fp_unarySucc).pair hr)).comp
    (ComplexityTypeQuery.fp_executeWithSpace L basis m space)
  exact ((hw.pair (hq.comp (fp_fst e.list (ComplexityTypeCache.cacheEncoding e)))).comp
    (ComplexityTypeCache.fp_member e)).congr (fun _ => by
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply,accepts,Nat.succ_eq_add_one,decide_eq_true_eq]; rfl)

theorem fp_candidates : FP (stateCode (d:=d) basis) wordCode (candidates L basis m space) :=
  ((fp_id _).pair (fp_const _ wordCode (List.range d))).comp
    (ListContextFilterMachines.fp_filterWithContext _ BitEncoding.nat
      (fun p => accepts L basis m space p.1 p.2) (fp_accepts L basis m space))

theorem fp_choose : FP (stateCode (d:=d) basis) (optionCode BitEncoding.nat) (choose L basis m space) :=
  (fp_candidates L basis m space).comp (fp_headOption BitEncoding.nat 0)

/-- Both the chosen-color and failure branches are compiled on all raw inputs. -/
theorem fp_step : FP (stateCode (d:=d) basis) (stateCode (d:=d) basis) (step L basis m space) := by
  let ei := stateCode (d:=d) basis
  have hc := fp_fst ((ComplexityTypeStackConcrete.contextCode basis).prod
    (ComplexityCSPMarginalRowBounds.labelEncoding basis d)) (BitEncoding.unaryNat.prod (wordCode.prod BitEncoding.bool))
  have hn := fp_len (d:=d) basis
  have ht := fp_target (d:=d) basis
  have hchoice := fp_choose L basis m space
  have hnone := hchoice.comp (fp_isNone BitEncoding.nat)
  have ha := hchoice.comp (fp_optionGetD BitEncoding.nat 0)
  have hr := (((hn.comp UnaryNatConversionMachine.fp_conversion).pair ha).pair ht).comp fp_replaceAt
  have hfail := hc.pair (hn.pair (ht.pair (fp_const ei BitEncoding.bool false)))
  have hsucc := hc.pair ((hn.comp fp_unarySucc).pair (hr.pair (fp_const ei BitEncoding.bool true)))
  have hlt := ((hn.comp UnaryNatConversionMachine.fp_conversion).pair
    (((fp_context basis).comp (ComplexityTypeStackConcrete.fp_dimensionOf basis)).comp
      UnaryNatConversionMachine.fp_conversion)).comp BinaryArithmetic.fp_comparison
  apply (fp_boolChoice ei ei (fp_alive basis)
    (fp_boolChoice ei ei hlt (fp_boolChoice ei ei hnone hfail hsucc) (fp_id ei)) (fp_id ei)).congr
  intro p
  unfold step
  cases he : choose L basis m space p <;> simp [he]

/-- Final reconstruction and literal encoded row comparison are also total FP. -/
theorem fp_finish : FP (stateCode (d:=d) basis) (optionCode wordCode) (finish L m) := by
  let ei := stateCode (d:=d) basis
  let e := ComplexityCSPMarginalRowBounds.labelEncoding basis d
  have hc := fp_context (d:=d) basis
  have hwanted := fp_wanted (d:=d) basis
  have hrec := (hc.pair ((fp_len basis).pair (fp_target basis))).comp
    (ComplexityTypeStackConcrete.fp_reconstruct basis m)
  have hword := hrec.comp (fp_optionGetD wordCode [])
  have heq := (((hc.pair hword).comp (ComplexityTypeStackConcrete.fp_rowLabelOf L basis m)).pair hwanted).comp
    (ComplexityEncodedEquality.fp_equal e)
  have hnone := hrec.comp (fp_isNone wordCode)
  have hsome := hword.comp (fp_some wordCode)
  have hnil := fp_const ei (optionCode wordCode) none
  apply (fp_boolChoice ei (optionCode wordCode) (fp_alive basis)
    (fp_boolChoice ei (optionCode wordCode) hnone hnil
      (fp_boolChoice ei (optionCode wordCode) heq hsome hnil)) hnil).congr
  intro p
  unfold finish
  cases he : ComplexityTypeStackConcrete.reconstruct m (context p,len p,target p) <;>
    simp [he,ComplexityEncodedEquality.equal,Option.filter]

end ComplexCSP.ComplexityLabelExtension
