import ComplexCSP.Complexity.ProjectedClosureSemantics
import ComplexCSP.Complexity.TypeStackCodecs
import ComplexCSP.Complexity.WitnessIteration
import PlanarHom.ListUnaryLengthMachine

/-! # Raw fixed-domain support-witness pin/drop primitives

All witness tables, targets and scope indices are literal runtime lists. The
finite operation and domain are program constants. Missing witnesses are empty
lists; a present zero-coordinate witness is the distinct singleton `[[]]`.
-/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open ComplexityWitnessPrimitives ComplexityWitnessEncoding ComplexityProjectedClosure
open ComplexityTypeStackMachines
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives

abbrev RawWitness := RawTable × MaybeWord
abbrev witnessCode : BitEncoding RawWitness := tableCode.prod maybeCode

variable (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d)

def storedRows (W : RawWitness) : Rows := W.2 ++ W.1.flatten.flatten

theorem fp_storedRows : FP witnessCode rowsCode storedRows := by
  have ht := ((fp_fst tableCode maybeCode).comp (ListFlattenMachines.fp_flatten maybeCode)).comp
    (ListFlattenMachines.fp_flatten wordCode)
  exact ((fp_snd tableCode maybeCode).pair ht).comp (ListMutationMachines.fp_append wordCode)

def first (rows : Rows) : MaybeWord := rows.head?.toList

theorem fp_first : FP rowsCode maybeCode first :=
  (fp_headOption wordCode []).transportOutput (fun _ => rfl)

theorem fp_isEmpty {A : Type} [DecidableEq A] (ea : BitEncoding A) :
    FP ea.list BitEncoding.bool (fun xs => decide (xs=[])) := by
  have h := ((ListCodecMachines.fp_length ea).pair (fp_const ea.list BitEncoding.nat 0)).comp
    NatListSumMachines.fp_equal
  exact h.congr (fun _ => by simp)

abbrev ForkInput := RawWitness × (ℕ × (ℕ × ℕ))
abbrev forkCode : BitEncoding ForkInput := witnessCode.prod (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat))

def forkTest (p : ForkInput) : Bool :=
  let u := tableLookup p.1.1 p.2.1 p.2.2.1
  let v := tableLookup p.1.1 p.2.1 p.2.2.2
  if u=[] then false else if v=[] then false else prefixEqual p.2.1 (u.headD []) (v.headD [])

theorem fp_forkTest : FP forkCode BitEncoding.bool forkTest := by
  have hW := fp_fst witnessCode (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat))
  have ht := hW.comp (fp_fst tableCode maybeCode)
  have hp := fp_snd witnessCode (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat))
  have hi := hp.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hab := hp.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have ha := hab.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hb := hab.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hu := (ht.pair (hi.pair ha)).comp fp_tableLookup
  have hv := (ht.pair (hi.pair hb)).comp fp_tableLookup
  have hue := hu.comp (fp_isEmpty wordCode)
  have hve := hv.comp (fp_isEmpty wordCode)
  have hpre := (hi.pair ((hu.comp (ListDecompositionMachines.fp_headD wordCode [])).pair
    (hv.comp (ListDecompositionMachines.fp_headD wordCode [])))).comp fp_prefixEqual
  exact hue.ite (fp_const forkCode BitEncoding.bool false)
    (hve.ite (fp_const forkCode BitEncoding.bool false) hpre)

abbrev CandidateInput := RawWitness × (ℕ × ℕ)
abbrev candidateCode : BitEncoding CandidateInput := witnessCode.prod (BitEncoding.nat.prod BitEncoding.nat)

def pinCandidates (p : CandidateInput) : Rows :=
  (projectedClosure d 2 m [0,p.2.2] (storedRows p.1)).filter (fun row => decide (row.getD 0 0 = p.2.1))

theorem fp_pinCandidates : FP candidateCode rowsCode (pinCandidates d m) := by
  have hW := fp_fst witnessCode (BitEncoding.nat.prod BitEncoding.nat)
  have hp := fp_snd witnessCode (BitEncoding.nat.prod BitEncoding.nat)
  have ha := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hi := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hsingle := (hi.pair (fp_const candidateCode wordCode [])).comp (ListMutationMachines.fp_cons BitEncoding.nat)
  have hscope := ((fp_const candidateCode BitEncoding.nat 0).pair hsingle).comp
    (ListMutationMachines.fp_cons BitEncoding.nat)
  have hrows := (hscope.pair (hW.comp fp_storedRows)).comp (fp_projectedClosure d 2 m)
  have hfrow := ((fp_snd BitEncoding.nat wordCode).pair
    (fp_const (BitEncoding.nat.prod wordCode) BitEncoding.nat 0)).comp (fp_getD BitEncoding.nat 0)
  have htest := (hfrow.pair (fp_fst BitEncoding.nat wordCode)).comp NatListSumMachines.fp_equal
  exact (ha.pair hrows).comp
    (ListContextFilterMachines.fp_filterWithContext BitEncoding.nat wordCode _ htest)

abbrev PinInput := RawWitness × (ℕ × (ℕ × ℕ))
abbrev pinCode : BitEncoding PinInput := forkCode

def pinAnchor (p : PinInput) : MaybeWord :=
  first ((pinCandidates d m (p.1,p.2.1,p.2.2.1)).filter
    (fun row => forkTest (p.1,p.2.2.1,row.getD p.2.2.1 0,p.2.2.2)))

theorem fp_pinAnchor : FP pinCode maybeCode (pinAnchor d m) := by
  have hW := fp_fst witnessCode (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat))
  have hp := fp_snd witnessCode (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat))
  have ha := hp.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hib := hp.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hi := hib.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hrows := (hW.pair (ha.pair hi)).comp (fp_pinCandidates d m)
  have hc := fp_fst pinCode wordCode
  have hrow := fp_snd pinCode wordCode
  have hW' := hc.comp hW
  have hi' := hc.comp hi
  have hb' := (hc.comp hib).comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hz := (hrow.pair hi').comp (fp_getD BitEncoding.nat 0)
  have hf := (hW'.pair (hi'.pair (hz.pair hb'))).comp fp_forkTest
  have hfilter := ((fp_id pinCode).pair hrows).comp
    (ListContextFilterMachines.fp_filterWithContext pinCode wordCode _ hf)
  exact hfilter.comp fp_first

def transport (p : RawWitness × (ℕ × (ℕ × List ℕ))) : MaybeWord :=
  repairWord d m (p.1.1,p.2.1,MaltsevTypeStack.replaceAt p.2.2.2 p.2.1 p.2.2.1,p.2.2.2)

abbrev transportCode := witnessCode.prod (BitEncoding.nat.prod (BitEncoding.nat.prod wordCode))

theorem fp_transport : FP transportCode maybeCode (transport d m) := by
  have hW := fp_fst witnessCode (BitEncoding.nat.prod (BitEncoding.nat.prod wordCode))
  have ht := hW.comp (fp_fst tableCode maybeCode)
  have hp := fp_snd witnessCode (BitEncoding.nat.prod (BitEncoding.nat.prod wordCode))
  have hi := hp.comp (fp_fst BitEncoding.nat (BitEncoding.nat.prod wordCode))
  have haw := hp.comp (fp_snd BitEncoding.nat (BitEncoding.nat.prod wordCode))
  have ha := haw.comp (fp_fst BitEncoding.nat wordCode)
  have hw := haw.comp (fp_snd BitEncoding.nat wordCode)
  have htarget := ((hi.pair ha).pair hw).comp fp_replaceAt
  exact (ht.pair (hi.pair (htarget.pair hw))).comp (fp_repairWord d m)

/-- Positive-coordinate pin lookup. Pin/drop discards coordinate zero, so only
this branch of the original pin-first constructor must be materialized. -/
def pinPositiveLookup (p : PinInput) : MaybeWord :=
  let anchor := pinAnchor d m p
  if anchor=[] then [] else transport d m (p.1,p.2.2.1,p.2.2.2,anchor.headD [])

theorem fp_pinPositiveLookup : FP pinCode maybeCode (pinPositiveLookup d m) := by
  have hW := fp_fst witnessCode (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat))
  have hib := (fp_snd witnessCode (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat))).comp
    (fp_snd BitEncoding.nat (BitEncoding.nat.prod BitEncoding.nat))
  have hi := hib.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hb := hib.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have ha := fp_pinAnchor d m
  have hz := ha.comp (fp_isEmpty wordCode)
  have hw := ha.comp (ListDecompositionMachines.fp_headD wordCode [])
  exact hz.ite (fp_const pinCode maybeCode [])
    ((hW.pair (hi.pair (hb.pair hw))).comp (fp_transport d m))

def pinDrop (p : RawWitness × ℕ) : RawWitness :=
  ((List.range p.1.1.tail.length).map (fun i =>
      (List.range d).map (fun b => (pinPositiveLookup d m (p.1,p.2,i+1,b)).map List.tail)),
    (tableLookup p.1.1 0 p.2).map List.tail)

/-- Actual polynomial-time materialization of a pinned-and-dropped witness.
Only the fixed two-coordinate closure budget d^2 is used by every lookup. -/
theorem fp_pinDrop : FP (witnessCode.prod BitEncoding.nat) witnessCode (pinDrop d m) := by
  let input := witnessCode.prod BitEncoding.nat
  have hW := fp_fst witnessCode BitEncoding.nat
  have ht := hW.comp (fp_fst tableCode maybeCode)
  have ha := fp_snd witnessCode BitEncoding.nat
  have htailMap : FP maybeCode maybeCode (fun ws : MaybeWord => ws.map List.tail) :=
    ListMapMachines.fp_map wordCode wordCode List.tail (ListDecompositionMachines.fp_tail BitEncoding.nat 0)
  have hs := ((ht.pair ((fp_const input BitEncoding.nat 0).pair ha)).comp fp_tableLookup).comp htailMap
  have hnum := (ht.comp (ListDecompositionMachines.fp_tail maybeCode.list [])).comp
    (ListUnaryLengthMachine.fp_length maybeCode.list)
  have hiList := hnum.comp ZeroOneSharpPMembership.fp_range
  let ctxt := input.prod BitEncoding.nat
  have hc := fp_fst ctxt BitEncoding.nat
  have hp := hc.comp (fp_fst input BitEncoding.nat)
  have hi := (hc.comp (fp_snd input BitEncoding.nat)).comp BinaryArithmetic.fp_successor
  have hb := fp_snd ctxt BitEncoding.nat
  have hbody := (((hp.comp hW).pair ((hp.comp ha).pair (hi.pair hb))).comp
    (fp_pinPositiveLookup d m)).comp htailMap
  have hrow := (((fp_id ctxt).pair (fp_const ctxt wordCode (List.range d))).comp
    (ListContextMachines.fp_mapWithContext ctxt BitEncoding.nat maybeCode _ hbody))
  have htable := ((fp_id input).pair hiList).comp
    (ListContextMachines.fp_mapWithContext input BitEncoding.nat maybeCode.list _ hrow)
  exact htable.pair hs

@[simp] theorem pinDrop_table_length (p : RawWitness × ℕ) :
    (pinDrop d m p).1.length = p.1.1.length-1 := by simp [pinDrop]

@[simp] theorem pinDrop_row_length (p : RawWitness × ℕ) (row : List MaybeWord)
    (h : row ∈ (pinDrop d m p).1) : row.length = d := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
  simp

end ComplexCSP.ComplexitySupportWitnessPrimitives
