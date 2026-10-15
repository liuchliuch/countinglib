import ComplexCSP.Complexity.WitnessPrefix
import ComplexCSP.Structure.MaltsevWitnessConstruction

/-! # Compiled local repair of a materialized finite-domain witness

The witness table is literal input data, not a function or oracle. Optional
vectors use zero-or-one-element lists, so an absent vector remains distinct from
a present vector of dimension zero. The raw machine is total on malformed tables.
-/
namespace ComplexCSP.ComplexityWitnessPrimitives
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines

abbrev MaybeWord := List (List ℕ)
abbrev RawTable := List (List MaybeWord)
abbrev maybeCode : BitEncoding MaybeWord := wordCode.list
abbrev tableCode : BitEncoding RawTable := maybeCode.list.list

/-- Two genuine runtime indexed lookups in the stored witness table. -/
def tableLookup (table : RawTable) (i a : ℕ) : MaybeWord :=
  (table.getD i []).getD a []

theorem fp_tableLookup :
    FP (tableCode.prod (BitEncoding.nat.prod BitEncoding.nat)) maybeCode
      (fun p => tableLookup p.1 p.2.1 p.2.2) := by
  have ht := fp_fst tableCode (BitEncoding.nat.prod BitEncoding.nat)
  have hp := fp_snd tableCode (BitEncoding.nat.prod BitEncoding.nat)
  have hi := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have ha := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hrow := (ht.pair hi).comp (fp_getD maybeCode.list [])
  exact (hrow.pair ha).comp (fp_getD maybeCode [])

private theorem fp_empty {A : Type} [DecidableEq A] (ea : BitEncoding A) :
    FP ea.list BitEncoding.bool (fun xs => decide (xs = [])) := by
  have hl := ListCodecMachines.fp_length ea
  exact ((hl.pair (fp_const ea.list BitEncoding.nat 0)).comp
    NatListSumMachines.fp_equal).congr (fun xs => by simp)

abbrev RepairInput := RawTable × (ℕ × (List ℕ × List ℕ))
abbrev repairCode : BitEncoding RepairInput :=
  tableCode.prod (BitEncoding.nat.prod (wordCode.prod wordCode))

/-- Total raw repair; absent anchors and failed prefix compatibility return none. -/
def repairWord (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d)
    (p : RepairInput) : MaybeWord :=
  let u := tableLookup p.1 p.2.1 (p.2.2.2.getD p.2.1 0)
  let v := tableLookup p.1 p.2.1 (p.2.2.1.getD p.2.1 0)
  if u = [] then [] else if v = [] then [] else
    if prefixEqual p.2.1 (u.headD []) (v.headD []) then
      [mapOperation d m p.2.2.2 (u.headD []) (v.headD [])]
    else []

/-- Actual bit-polynomial repair with an arbitrary runtime materialized table. -/
theorem fp_repairWord (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d) :
    FP repairCode maybeCode (repairWord d m) := by
  have ht := fp_fst tableCode (BitEncoding.nat.prod (wordCode.prod wordCode))
  have hp := fp_snd tableCode (BitEncoding.nat.prod (wordCode.prod wordCode))
  have hi := hp.comp (fp_fst BitEncoding.nat (wordCode.prod wordCode))
  have hw := hp.comp (fp_snd BitEncoding.nat (wordCode.prod wordCode))
  have htarget := hw.comp (fp_fst wordCode wordCode)
  have hcurrent := hw.comp (fp_snd wordCode wordCode)
  have hc := (hcurrent.pair hi).comp (fp_getD BitEncoding.nat 0)
  have hx := (htarget.pair hi).comp (fp_getD BitEncoding.nat 0)
  have hu := (ht.pair (hi.pair hc)).comp fp_tableLookup
  have hv := (ht.pair (hi.pair hx)).comp fp_tableLookup
  have hue := hu.comp (fp_empty wordCode)
  have hve := hv.comp (fp_empty wordCode)
  have hul := hu.comp (ListDecompositionMachines.fp_headD wordCode [])
  have hvl := hv.comp (ListDecompositionMachines.fp_headD wordCode [])
  have hpre := (hi.pair (hul.pair hvl)).comp fp_prefixEqual
  have hpre' : FP repairCode BitEncoding.bool (fun p =>
      decide (prefixEqual p.2.1
        ((tableLookup p.1 p.2.1 (p.2.2.2.getD p.2.1 0)).headD [])
        ((tableLookup p.1 p.2.1 (p.2.2.1.getD p.2.1 0)).headD []) = true)) :=
    hpre.congr (fun _ => by simp)
  have hm := (hcurrent.pair (hul.pair hvl)).comp (fp_mapOperation d m)
  have hsome := (hm.pair (fp_const repairCode maybeCode [])).comp
    (ListMutationMachines.fp_cons wordCode)
  have hnone := fp_const repairCode maybeCode []
  exact hue.ite hnone (hve.ite hnone (hpre'.ite hsome hnone))

end ComplexCSP.ComplexityWitnessPrimitives

namespace ComplexCSP.ComplexityWitnessEncoding
open MaltsevWitness MaltsevRelations ComplexityWitnessPrimitives

def maybeWord {d n : ℕ} (x : Option (Tuple (Fin d) n)) : MaybeWord := x.toList.map word

def rawTable {d n : ℕ} (W : StoredCode d n) : RawTable :=
  W.table.toList.map (fun row => row.toList.map maybeWord)

@[simp] theorem tableLookup_stored {d n : ℕ} (W : StoredCode d n)
    (i : Fin n) (a : Fin d) :
    tableLookup (rawTable W) i.val a.val = maybeWord (W.toCode.lookup i a) := by
  simp [tableLookup, rawTable, StoredCode.toCode, List.getD_eq_getElem?_getD]

/-- The literal raw repair machine matches the witness algorithm on stored
valid tuples; zero-length present vectors and missing anchors stay distinct. -/
theorem repairWord_stored {d n : ℕ} (m : Operation (Fin d)) (W : StoredCode d n)
    (i : Fin n) (target current : Tuple (Fin d) n) :
    repairWord d (fun a b c => m (a,b,c))
      (rawTable W, i.val, word target, word current) =
        maybeWord (MaltsevWitness.repair m W.toCode i target current) := by
  simp only [repairWord, word_getD, tableLookup_stored]
  cases hu : W.toCode.lookup i (view current i) with
  | none => simp [hu, MaltsevWitness.repair, maybeWord]
  | some u =>
    cases hv : W.toCode.lookup i (view target i) with
    | none => simp [hu, hv, MaltsevWitness.repair, maybeWord]
    | some v =>
      by_cases hp : ∀ j : Fin n, j.val < i.val → view u j = view v j
      · have hb := (prefixEqual_word i.val u v).mpr hp
        have hr : MaltsevWitness.repair m W.toCode i target current =
            some (Vector.ofFn (map₃ m (view current) (view u) (view v))) := by
          simp only [MaltsevWitness.repair, hu, hv]
          dsimp only [Bind.bind, Option.bind]
          rw [if_pos hp]
          rfl
        rw [hr]
        simpa [hu, hv, maybeWord, hb] using
          congrArg (fun x => [x]) (mapOperation_word m current u v)
      · have hb : prefixEqual i.val (word u) (word v) = false := by
          apply Bool.eq_false_iff.mpr
          intro h
          exact hp ((prefixEqual_word i.val u v).mp h)
        have hr : MaltsevWitness.repair m W.toCode i target current = none := by
          simp only [MaltsevWitness.repair, hu, hv]
          dsimp only [Bind.bind, Option.bind]
          rw [if_neg hp]
        rw [hr]
        simp [maybeWord, hb]

end ComplexCSP.ComplexityWitnessEncoding
