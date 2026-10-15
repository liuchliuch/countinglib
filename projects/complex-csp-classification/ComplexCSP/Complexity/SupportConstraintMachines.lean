import ComplexCSP.Complexity.SupportSafeInputs
import Mathlib.Logic.Equiv.Finset
import Mathlib.Logic.Encodable.Pi

/-! # Actual fixed-arity support-constraint insertion submachines

The relation's Boolean table and its arity are fixed program constants. Runtime
scopes, tuple words, indices and witness tables are fully materialized. Eager
extension probes prepare a safe target even when their candidate is missing.
-/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityProjectedClosure ComplexityTypeStackMachines
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives
variable {d r : ℕ}

private def assignments : List (Fin r → Fin d) :=
  List.ofFn ((Encodable.fintypeEquivFin (α:=Fin r → Fin d)).symm)

private theorem mem_assignments (a : Fin r → Fin d) : a ∈ assignments := by
  exact List.mem_ofFn.mpr ⟨Encodable.fintypeEquivFin a,Equiv.symm_apply_apply _ a⟩

def acceptKeys (accept : (Fin r → Fin d) → Bool) : Rows :=
  (assignments.filter accept).map keyWord

def acceptWord (accept : (Fin r → Fin d) → Bool) (w : List ℕ) : Bool :=
  decide (w ∈ acceptKeys accept)

theorem fp_acceptWord (accept : (Fin r → Fin d) → Bool) :
    FP wordCode BitEncoding.bool (acceptWord accept) := by
  exact (((fp_id wordCode).pair (fp_const wordCode rowsCode (acceptKeys accept))).comp
    (ComplexityTypeCache.fp_member wordCode)).congr (fun _ => by simp [acceptWord])

theorem acceptWord_key (accept : (Fin r → Fin d) → Bool) (a : Fin r → Fin d) :
    acceptWord accept (keyWord a) = accept a := by
  apply Bool.eq_iff_iff.mpr
  simp only [acceptWord,decide_eq_true_eq,acceptKeys,List.mem_map,List.mem_filter]
  constructor
  · rintro ⟨b,⟨_,hb⟩,he⟩
    have hba := keyWord_injective he
    subst b
    exact hb
  · intro ha
    exact ⟨a,⟨mem_assignments a,ha⟩,rfl⟩

def filterAccepted (accept : (Fin r → Fin d) → Bool) (scope : List ℕ) (rows : Rows) : Rows :=
  rows.filter (fun row => acceptWord accept (project scope row))

theorem fp_filterAccepted (accept : (Fin r → Fin d) → Bool) :
    FP (wordCode.prod rowsCode) rowsCode (fun p => filterAccepted accept p.1 p.2) :=
  ListContextFilterMachines.fp_filterWithContext wordCode wordCode _
    (fp_project.comp (fp_acceptWord accept))

variable (m : Fin d → Fin d → Fin d → Fin d)

def constraintSeeds (accept : (Fin r → Fin d) → Bool) (p : RawWitness × List ℕ) : Rows :=
  filterAccepted accept p.2 (projectedClosure d r m p.2 (storedRows p.1))

theorem fp_constraintSeeds (accept : (Fin r → Fin d) → Bool) :
    FP (witnessCode.prod wordCode) rowsCode (constraintSeeds m accept) := by
  have hW := fp_fst witnessCode wordCode
  have hs := fp_snd witnessCode wordCode
  have hr := (hs.pair (hW.comp fp_storedRows)).comp (fp_projectedClosure d r m)
  exact (hs.pair hr).comp (fp_filterAccepted accept)

def constraintCandidates (accept : (Fin r → Fin d) → Bool)
    (p : (RawWitness × List ℕ) × ℕ) : Rows :=
  filterAccepted accept p.1.2 (projectedClosure d (r+1) m (p.2::p.1.2) (storedRows p.1.1))

theorem fp_constraintCandidates (accept : (Fin r → Fin d) → Bool) :
    FP ((witnessCode.prod wordCode).prod BitEncoding.nat) rowsCode (constraintCandidates m accept) := by
  have hp := fp_fst (witnessCode.prod wordCode) BitEncoding.nat
  have hW := hp.comp (fp_fst witnessCode wordCode)
  have hs := hp.comp (fp_snd witnessCode wordCode)
  have hi := fp_snd (witnessCode.prod wordCode) BitEncoding.nat
  have hscope := (hi.pair hs).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  have hr := (hscope.pair (hW.comp fp_storedRows)).comp (fp_projectedClosure d (r+1) m)
  exact (hs.pair hr).comp (fp_filterAccepted accept)

def positiveOfScope (p : {p : RawWitness × List ℕ // ScopeInputValid (d:=d) r p}) :
    {W : RawWitness // PositiveWitness (d:=d) W} :=
  ⟨p.val.1,by obtain ⟨n,hn,W,ρ,hW,_⟩ := p.property; exact ⟨n,hn,W,hW⟩⟩

theorem fp_scopeView : FP (validScopeInputCode d r) (witnessCode.prod wordCode) (fun p => p.val) :=
  fp_code_view _ _ _ (fun _ => rfl)

theorem fp_positiveOfScope : FP (validScopeInputCode d r) (positiveWitnessCode d) positiveOfScope :=
  (fp_scopeView.comp (fp_fst witnessCode wordCode)).transportOutput (fun _ => rfl)

abbrev ExtensionInput := (RawWitness × List ℕ) × (ℕ × (ℕ × List ℕ))
abbrev extensionTailCode := BitEncoding.nat.prod (BitEncoding.nat.prod wordCode)

def constraintExtension (accept : (Fin r → Fin d) → Bool) (p : ExtensionInput) : MaybeWord :=
  let target := MaltsevTypeStack.replaceAt p.2.2.2 p.2.1 p.2.2.1
  let frames := prefixFrame d m (p.1.1,safeTarget d (p.1.1,target),p.2.1+1)
  first (filterAccepted accept p.1.2 (projectedClosure d r m p.1.2 frames))

theorem fp_constraintExtension (accept : (Fin r → Fin d) → Bool) :
    FP ((validScopeInputCode d r).prod extensionTailCode) maybeCode
      (fun p => constraintExtension m accept (p.1.val,p.2)) := by
  let e := (validScopeInputCode d r).prod extensionTailCode
  have hp := fp_fst (validScopeInputCode d r) extensionTailCode
  have hraw := hp.comp fp_scopeView
  have hpositive := hp.comp fp_positiveOfScope
  have hs := hraw.comp (fp_snd witnessCode wordCode)
  have hargs := fp_snd (validScopeInputCode d r) extensionTailCode
  have hi := hargs.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod wordCode))
  have haw := hargs.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod wordCode))
  have ha := haw.comp (fp_fst BitEncoding.nat wordCode)
  have hw := haw.comp (fp_snd BitEncoding.nat wordCode)
  have ht := ((hi.pair ha).pair hw).comp fp_replaceAt
  have hk := hi.comp BinaryArithmetic.fp_successor
  have hf := (hpositive.pair (ht.pair hk)).comp (fp_safePrefixFrame m)
  have hcl := (hs.pair hf).comp (fp_projectedClosure d r m)
  exact ((hs.pair hcl).comp (fp_filterAccepted accept)).comp fp_first

abbrev ConstraintQuery := (RawWitness × List ℕ) × (ℕ × ℕ)
abbrev queryTailCode := BitEncoding.nat.prod BitEncoding.nat

def constraintAnchor (accept : (Fin r → Fin d) → Bool) (p : ConstraintQuery) : MaybeWord :=
  first ((constraintCandidates m accept (p.1,p.2.1)).filter
    (fun row => !(decide (constraintExtension m accept (p.1,p.2.1,p.2.2,row)=[]))))

theorem fp_constraintAnchor (accept : (Fin r → Fin d) → Bool) :
    FP ((validScopeInputCode d r).prod queryTailCode) maybeCode
      (fun p => constraintAnchor m accept (p.1.val,p.2)) := by
  let ctxt := (validScopeInputCode d r).prod queryTailCode
  have hp := fp_fst (validScopeInputCode d r) queryTailCode
  have hraw := hp.comp fp_scopeView
  have hia := fp_snd (validScopeInputCode d r) queryTailCode
  have hi := hia.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hcandidates := (hraw.pair hi).comp (fp_constraintCandidates m accept)
  have hcontext := fp_fst ctxt wordCode
  have hp' := hcontext.comp hp
  have hargs := hcontext.comp hia
  have hi' := hargs.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have ha' := hargs.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hrow := fp_snd ctxt wordCode
  have hext := (hp'.pair (hi'.pair (ha'.pair hrow))).comp (fp_constraintExtension m accept)
  have hempty := hext.comp (fp_isEmpty wordCode)
  have htest := hempty.comp (fp_bool_unary BitEncoding.bool not)
  exact (((fp_id ctxt).pair hcandidates).comp
    (ListContextFilterMachines.fp_filterWithContext ctxt wordCode _ htest)).comp fp_first

def insertLookup (accept : (Fin r → Fin d) → Bool) (p : ConstraintQuery) : MaybeWord :=
  let anchor := constraintAnchor m accept p
  if anchor=[] then [] else constraintExtension m accept (p.1,p.2.1,p.2.2,anchor.headD [])

theorem fp_insertLookup (accept : (Fin r → Fin d) → Bool) :
    FP ((validScopeInputCode d r).prod queryTailCode) maybeCode
      (fun p => insertLookup m accept (p.1.val,p.2)) := by
  let e := (validScopeInputCode d r).prod queryTailCode
  have hp := fp_fst (validScopeInputCode d r) queryTailCode
  have hargs := fp_snd (validScopeInputCode d r) queryTailCode
  have hi := hargs.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have ha := hargs.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hanchor := fp_constraintAnchor m accept
  have hz := hanchor.comp (fp_isEmpty wordCode)
  have hw := hanchor.comp (ListDecompositionMachines.fp_headD wordCode [])
  exact hz.ite (fp_const e maybeCode [])
    ((hp.pair (hi.pair (ha.pair hw))).comp (fp_constraintExtension m accept))

def insertConstraint (accept : (Fin r → Fin d) → Bool) (p : RawWitness × List ℕ) : RawWitness :=
  ((List.range p.1.1.length).map (fun i => (List.range d).map (fun a => insertLookup m accept (p,i,a))),
    first (constraintSeeds m accept p))

/-- The full table is materialized by n*d lookups, with n read in unary from the
actual table list. Every extension probe uses fixed-arity projected closure. -/
theorem fp_insertConstraint (accept : (Fin r → Fin d) → Bool) :
    FP (validScopeInputCode d r) witnessCode (fun p => insertConstraint m accept p.val) := by
  have hraw := fp_scopeView (d:=d) (r:=r)
  have hW := hraw.comp (fp_fst witnessCode wordCode)
  have hn := (hW.comp (fp_fst tableCode maybeCode)).comp (ListUnaryLengthMachine.fp_length maybeCode.list)
  have his := hn.comp ZeroOneSharpPMembership.fp_range
  let ctxt := (validScopeInputCode d r).prod BitEncoding.nat
  have hc := fp_fst ctxt BitEncoding.nat
  have hp := hc.comp (fp_fst (validScopeInputCode d r) BitEncoding.nat)
  have hi := hc.comp (fp_snd (validScopeInputCode d r) BitEncoding.nat)
  have ha := fp_snd ctxt BitEncoding.nat
  have hcell := (hp.pair (hi.pair ha)).comp (fp_insertLookup m accept)
  have hrow := (((fp_id ctxt).pair (fp_const ctxt wordCode (List.range d))).comp
    (ListContextMachines.fp_mapWithContext ctxt BitEncoding.nat maybeCode _ hcell))
  have htable := ((fp_id (validScopeInputCode d r)).pair his).comp
    (ListContextMachines.fp_mapWithContext (validScopeInputCode d r) BitEncoding.nat maybeCode.list _ hrow)
  have hseed := (hraw.comp (fp_constraintSeeds m accept)).comp fp_first
  exact htable.pair hseed

end ComplexCSP.ComplexitySupportWitnessPrimitives
