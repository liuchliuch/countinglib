import ComplexCSP.Complexity.SupportWitnessPrimitives
import ComplexCSP.Complexity.WitnessReconstruction
import ComplexCSP.Structure.MaltsevWitnessUnion

/-! # Actual materialized union-witness compiler

The union algorithm uses literal lists of stored witnesses. Candidate selection,
prefix reconstruction and coherent first-anchor selection are actual machines;
there is no union or relation-membership oracle. All raw inputs are total.
-/
namespace ComplexCSP.ComplexityWitnessUnion
open ComplexityWitnessPrimitives ComplexitySupportWitnessPrimitives ComplexityTypeStackMachines
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
variable {d : ℕ} (m : Fin d → Fin d → Fin d → Fin d)

abbrev Family := List RawWitness
abbrev familyCode : BitEncoding Family := witnessCode.list
abbrev ExtensionInput := Family × (ℕ × (ℕ × List ℕ))
abbrev extensionCode : BitEncoding ExtensionInput :=
  familyCode.prod (BitEncoding.unaryNat.prod (BitEncoding.nat.prod wordCode))

def extension (p : ExtensionInput) : MaybeWord :=
  ((p.1.flatMap fun W => reconstructRawTo d m W.1
    (MaltsevTypeStack.replaceAt p.2.2.2 p.2.1 p.2.2.1) W.2 (p.2.1+1)).head?).toList

theorem fp_extension : FP extensionCode maybeCode (extension m) := by
  have hc := fp_fst extensionCode witnessCode
  have hW := fp_snd extensionCode witnessCode
  have hp := hc.comp (fp_snd familyCode (BitEncoding.unaryNat.prod (BitEncoding.nat.prod wordCode)))
  have hi := hp.comp (fp_fst BitEncoding.unaryNat (BitEncoding.nat.prod wordCode))
  have hin := hi.comp UnaryNatConversionMachine.fp_conversion
  have haw := hp.comp (fp_snd BitEncoding.unaryNat (BitEncoding.nat.prod wordCode))
  have ha := haw.comp (fp_fst BitEncoding.nat wordCode)
  have hw := haw.comp (fp_snd BitEncoding.nat wordCode)
  have htarget := ((hin.pair ha).pair hw).comp fp_replaceAt
  have hlen := hi.comp fp_unarySucc
  have ht := hW.comp (fp_fst tableCode maybeCode)
  have hs := hW.comp (fp_snd tableCode maybeCode)
  have hrow := (hlen.pair (ht.pair (htarget.pair hs))).comp (fp_reconstructRawTo d m)
  have hlist := ((fp_id extensionCode).pair
    (fp_fst familyCode (BitEncoding.unaryNat.prod (BitEncoding.nat.prod wordCode)))).comp
    (ListContextMachines.fp_mapWithContext extensionCode witnessCode maybeCode _ hrow)
  exact (hlist.comp (ListFlattenMachines.fp_flatten wordCode)).comp fp_first

abbrev CandidateInput := Family × ℕ
abbrev candidateCode : BitEncoding CandidateInput := familyCode.prod BitEncoding.nat

def candidates (p : CandidateInput) : List (List ℕ) :=
  p.1.flatMap (fun W => (W.1.getD p.2 []).flatten)

theorem fp_candidates : FP candidateCode wordCode.list candidates := by
  have hi := fp_fst BitEncoding.nat witnessCode
  have ht := (fp_snd BitEncoding.nat witnessCode).comp (fp_fst tableCode maybeCode)
  have hr := ((ht.pair hi).comp (fp_getD maybeCode.list [])).comp
    (ListFlattenMachines.fp_flatten wordCode)
  have hlist := ((fp_snd familyCode BitEncoding.nat).pair (fp_fst familyCode BitEncoding.nat)).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.nat witnessCode wordCode.list _ hr)
  exact hlist.comp (ListFlattenMachines.fp_flatten wordCode)

abbrev LookupInput := Family × (ℕ × ℕ)
abbrev lookupCode : BitEncoding LookupInput := familyCode.prod (BitEncoding.unaryNat.prod BitEncoding.nat)

def anchor (p : LookupInput) : MaybeWord :=
  first ((candidates (p.1,p.2.1)).filter (fun z => decide (extension m (p.1,p.2.1,p.2.2,z) ≠ [])))

theorem fp_anchor : FP lookupCode maybeCode (anchor m) := by
  have hF := fp_fst familyCode (BitEncoding.unaryNat.prod BitEncoding.nat)
  have hia := fp_snd familyCode (BitEncoding.unaryNat.prod BitEncoding.nat)
  have hi := hia.comp (fp_fst BitEncoding.unaryNat BitEncoding.nat)
  have hcand := (hF.pair (hi.comp UnaryNatConversionMachine.fp_conversion)).comp fp_candidates
  have hc := fp_fst lookupCode wordCode
  have hF' := hc.comp hF
  have hia' := hc.comp hia
  have hi' := hia'.comp (fp_fst BitEncoding.unaryNat BitEncoding.nat)
  have ha := hia'.comp (fp_snd BitEncoding.unaryNat BitEncoding.nat)
  have hz := fp_snd lookupCode wordCode
  have he := (hF'.pair (hi'.pair (ha.pair hz))).comp (fp_extension m)
  have ht := (he.comp (ComplexitySupportWitnessPrimitives.fp_isEmpty wordCode)).ite
    (fp_const (lookupCode.prod wordCode) BitEncoding.bool false)
    (fp_const (lookupCode.prod wordCode) BitEncoding.bool true)
  have ht' : FP (lookupCode.prod wordCode) BitEncoding.bool
      (fun p => decide (extension m (p.1.1,p.1.2.1,p.1.2.2,p.2) ≠ [])) :=
    ht.congr (fun p => by simp)
  exact (((fp_id lookupCode).pair hcand).comp
    (ListContextFilterMachines.fp_filterWithContext lookupCode wordCode _ ht')).comp fp_first

def lookup (p : LookupInput) : MaybeWord :=
  let z := anchor m p
  if z=[] then [] else extension m (p.1,p.2.1,p.2.2,z.headD [])

theorem fp_lookup : FP lookupCode maybeCode (lookup m) := by
  have hF := fp_fst familyCode (BitEncoding.unaryNat.prod BitEncoding.nat)
  have hia := fp_snd familyCode (BitEncoding.unaryNat.prod BitEncoding.nat)
  have hi := hia.comp (fp_fst BitEncoding.unaryNat BitEncoding.nat)
  have ha := hia.comp (fp_snd BitEncoding.unaryNat BitEncoding.nat)
  have hz := fp_anchor m
  have he := hz.comp (ComplexitySupportWitnessPrimitives.fp_isEmpty wordCode)
  have hw := hz.comp (ListDecompositionMachines.fp_headD wordCode [])
  exact he.ite (fp_const lookupCode maybeCode [])
    ((hF.pair (hi.pair (ha.pair hw))).comp (fp_extension m))

abbrev BuildInput := ℕ × Family
abbrev buildCode : BitEncoding BuildInput := BitEncoding.unaryNat.prod familyCode

def build (p : BuildInput) : RawWitness :=
  ((List.range p.1).map (fun i => (List.range d).map (fun a => lookup m (p.2,i,a))),
    first (p.2.flatMap Prod.snd))

theorem fp_unaryRange : FP BitEncoding.unaryNat BitEncoding.unaryNat.list List.range := by
  have hmin : FP (BitEncoding.unaryNat.prod BitEncoding.nat) BitEncoding.unaryNat
      (fun p => min p.1 p.2) := ⟨BoundedUnaryMachines.computer⟩
  have hmap := ((fp_id BitEncoding.unaryNat).pair ZeroOneSharpPMembership.fp_range).comp
    (ListContextMachines.fp_mapWithContext BitEncoding.unaryNat BitEncoding.nat BitEncoding.unaryNat _ hmin)
  apply hmap.congr
  intro n
  simp only [Function.comp_apply,id_eq]
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp only [List.getElem_map,List.getElem_range]
    exact min_eq_right (by simpa using (Nat.le_of_lt hi'))

theorem fp_build : FP buildCode witnessCode (build m) := by
  have hF := fp_fst familyCode BitEncoding.unaryNat
  have hi := fp_snd familyCode BitEncoding.unaryNat
  have hc := fp_fst (familyCode.prod BitEncoding.unaryNat) BitEncoding.nat
  have ha := fp_snd (familyCode.prod BitEncoding.unaryNat) BitEncoding.nat
  have hval := ((hc.comp hF).pair ((hc.comp hi).pair ha)).comp (fp_lookup m)
  have hrow := ((fp_id (familyCode.prod BitEncoding.unaryNat)).pair
    (fp_const (familyCode.prod BitEncoding.unaryNat) wordCode (List.range d))).comp
      (ListContextMachines.fp_mapWithContext (familyCode.prod BitEncoding.unaryNat)
        BitEncoding.nat maybeCode _ hval)
  have hindices := (fp_fst BitEncoding.unaryNat familyCode).comp fp_unaryRange
  have htable := ((fp_snd BitEncoding.unaryNat familyCode).pair hindices).comp
    (ListContextMachines.fp_mapWithContext familyCode BitEncoding.unaryNat maybeCode.list _ hrow)
  have hseeds := ((fp_snd BitEncoding.unaryNat familyCode).comp
    (ListMapMachines.fp_map witnessCode maybeCode Prod.snd (fp_snd tableCode maybeCode))).comp
      (ListFlattenMachines.fp_flatten wordCode)
  exact (htable.pair (hseeds.comp fp_first)).congr (fun _ => rfl)

end ComplexCSP.ComplexityWitnessUnion
