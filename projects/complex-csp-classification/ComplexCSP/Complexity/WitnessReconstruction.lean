import ComplexCSP.Complexity.WitnessIteration
import PlanarHom.ListUnaryLengthMachine

/-! # Actual polynomial-time materialized witness reconstruction

The loop budget is unary, or computed from the actual target-word length. The
fixed table and target are carried unchanged; coordinate indices come from a
materialized range. Intermediate bounds are the proved literal bounds from
ComplexityWitnessIteration, not supplied compiler or size assumptions.
-/
set_option maxHeartbeats 2000000
namespace ComplexCSP.ComplexityWitnessPrimitives
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives

variable (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d)

private theorem fp_maybeEmpty : FP maybeCode BitEncoding.bool
    (fun cur : MaybeWord => decide (cur = [])) := by
  exact (((ListCodecMachines.fp_length wordCode).pair
    (fp_const maybeCode BitEncoding.nat 0)).comp NatListSumMachines.fp_equal).congr
      (fun cur => by simp)

/-- Compile the actual missing-current guard and raw repair into an FP step. -/
theorem fp_advance : FP (witnessStateCode.prod BitEncoding.nat) maybeCode
    (fun p => advance d m p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  let e := witnessStateCode.prod BitEncoding.nat
  have hs := fp_fst witnessStateCode BitEncoding.nat
  have hi := fp_snd witnessStateCode BitEncoding.nat
  have ht := hs.comp (fp_fst tableCode (wordCode.prod maybeCode))
  have hp := hs.comp (fp_snd tableCode (wordCode.prod maybeCode))
  have htarget := hp.comp (fp_fst wordCode maybeCode)
  have hcur := hp.comp (fp_snd wordCode maybeCode)
  have he := hcur.comp fp_maybeEmpty
  have hhead := hcur.comp (ListDecompositionMachines.fp_headD wordCode [])
  have harg := ht.pair (hi.pair (htarget.pair hhead))
  have hr := harg.comp (fp_repairWord d m)
  exact he.ite (fp_const e maybeCode []) hr

/-- The finite table and target remain in the state, with no growing counter. -/
theorem fp_witnessStep : FP (witnessStateCode.prod BitEncoding.nat) witnessStateCode
    (fun p => witnessStep d m p.1 p.2) := by
  have hs := fp_fst witnessStateCode BitEncoding.nat
  have ht := hs.comp (fp_fst tableCode (wordCode.prod maybeCode))
  have htarget := (hs.comp (fp_snd tableCode (wordCode.prod maybeCode))).comp
    (fp_fst wordCode maybeCode)
  exact ht.pair (htarget.pair (fp_advance d m))

/-- Full actual fold compiler, with the proved linear intermediate-state bound. -/
theorem fp_foldWitnessState : FP (witnessStateCode.prod BitEncoding.nat.list) witnessStateCode
    (fun p => p.2.foldl (witnessStep d m) p.1) :=
  ListFoldMachines.fp_foldl BitEncoding.nat witnessStateCode (witnessStep d m)
    (fp_witnessStep d m) (Polynomial.C (100*(d+1)+2) * (Polynomial.X+1))
    (fun state indices i _ => witnessStep_prefix_bound d m state indices i)

/-- Literal raw iteration of the coordinate repairs. -/
def reconstructRawTo (table : RawTable) (target : List ℕ) (seed : MaybeWord)
    (k : ℕ) : MaybeWord :=
  (List.range k).foldl (advance d m table target) seed

/-- A unary budget produces an actual materialized coordinate list and fold. -/
theorem fp_reconstructRawTo : FP (BitEncoding.unaryNat.prod witnessStateCode) maybeCode
    (fun p => reconstructRawTo d m p.2.1 p.2.2.1 p.2.2.2 p.1) := by
  have hk := fp_fst BitEncoding.unaryNat witnessStateCode
  have hs := fp_snd BitEncoding.unaryNat witnessStateCode
  have hindices := hk.comp ZeroOneSharpPMembership.fp_range
  have hf := (hs.pair hindices).comp (fp_foldWitnessState d m)
  have hout := (hf.comp (fp_snd tableCode (wordCode.prod maybeCode))).comp
    (fp_snd wordCode maybeCode)
  exact hout.congr (fun p => by
    rcases p with ⟨k,table,target,seed⟩
    simp only [Function.comp_apply,fold_witnessStep]
    rfl)

/-- Full dimension is obtained from the materialized target, not a binary
counter that could encode exponentially many absent coordinates. -/
def reconstructRaw (state : WitnessState) : MaybeWord :=
  reconstructRawTo d m state.1 state.2.1 state.2.2 state.2.1.length

theorem fp_reconstructRaw : FP witnessStateCode maybeCode (reconstructRaw d m) := by
  have ht := (fp_snd tableCode (wordCode.prod maybeCode)).comp
    (fp_fst wordCode maybeCode)
  have hn := ht.comp (ListUnaryLengthMachine.fp_length BitEncoding.nat)
  exact (hn.pair (fp_id witnessStateCode)).comp (fp_reconstructRawTo d m)

/-- A present singleton output must have exactly the target length and entries.
The empty optional output is distinct from a present dimension-zero vector. -/
def memberRaw (state : WitnessState) : Bool :=
  let result := reconstructRaw d m state
  decide (result.length = 1) && decide ((result.headD []).length = state.2.1.length) &&
    prefixEqual state.2.1.length (result.headD []) state.2.1

theorem fp_memberRaw : FP witnessStateCode BitEncoding.bool (memberRaw d m) := by
  have hr := fp_reconstructRaw d m
  have ht := (fp_snd tableCode (wordCode.prod maybeCode)).comp (fp_fst wordCode maybeCode)
  have hcount := hr.comp (ListCodecMachines.fp_length wordCode)
  have hone := (hcount.pair (fp_const witnessStateCode BitEncoding.nat 1)).comp
    NatListSumMachines.fp_equal
  have hhead := hr.comp (ListDecompositionMachines.fp_headD wordCode [])
  have hheadlen := hhead.comp (ListCodecMachines.fp_length BitEncoding.nat)
  have htargetlen := ht.comp (ListCodecMachines.fp_length BitEncoding.nat)
  have hlen := (hheadlen.pair htargetlen).comp NatListSumMachines.fp_equal
  have hprefix := (htargetlen.pair (hhead.pair ht)).comp fp_prefixEqual
  exact (((hone.pair hlen).comp (fp_bool_gate (fun p => p.1 && p.2))).pair hprefix).comp
    (fp_bool_gate (fun p => p.1 && p.2))

end ComplexCSP.ComplexityWitnessPrimitives

namespace ComplexCSP.ComplexityWitnessEncoding
open MaltsevWitness MaltsevRelations ComplexityWitnessPrimitives

/-- One raw advance is the precise optional typed repair, with no algebraic
assumptions on the operation needed for implementation agreement. -/
theorem advance_maybeWord_stored {d n : ℕ} (m : Operation (Fin d))
    (W : StoredCode d n) (target : Tuple (Fin d) n)
    (cur : Option (Tuple (Fin d) n)) (i : Fin n) :
    advance d (fun a b c => m (a,b,c)) (rawTable W) (word target) (maybeWord cur) i.val =
      maybeWord (cur.bind (fun current => MaltsevWitness.repair m W.toCode i target current)) := by
  cases cur with
  | none => simp [advance,maybeWord]
  | some current =>
    simpa [advance,maybeWord] using repairWord_stored m W i target current

/-- The full raw loop agrees with the mathematical recursion for every valid
prefix budget. It does not claim the unguarded raw loop agrees beyond n. -/
theorem reconstructRawTo_stored {d n : ℕ} (m : Operation (Fin d))
    (W : StoredCode d n) (target : Tuple (Fin d) n) (k : ℕ) (hk : k ≤ n) :
    reconstructRawTo d (fun a b c => m (a,b,c))
      (rawTable W) (word target) (maybeWord W.seed) k =
        maybeWord (MaltsevWitness.reconstructTo m W.toCode target k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k < n := by omega
    have he := ih (by omega)
    unfold reconstructRawTo
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    change advance d (fun a b c => m (a,b,c)) (rawTable W) (word target)
      (reconstructRawTo d (fun a b c => m (a,b,c))
        (rawTable W) (word target) (maybeWord W.seed) k) k = _
    rw [he]
    simpa [MaltsevWitness.reconstructTo,hkn] using
      advance_maybeWord_stored m W target
        (MaltsevWitness.reconstructTo m W.toCode target k) ⟨k,hkn⟩

/-- The literal materialized state supplied to the proved FP programs. -/
def storedState {d n : ℕ} (W : StoredCode d n) (target : Tuple (Fin d) n) : WitnessState :=
  (rawTable W,word target,maybeWord W.seed)

theorem reconstructRaw_stored {d n : ℕ} (m : Operation (Fin d))
    (W : StoredCode d n) (target : Tuple (Fin d) n) :
    reconstructRaw d (fun a b c => m (a,b,c)) (storedState W target) =
      maybeWord (MaltsevWitness.reconstructTo m W.toCode target n) := by
  simpa only [reconstructRaw,storedState,word_length] using
    reconstructRawTo_stored m W target n le_rfl

/-- Exact membership equality with the previously proved typed algorithm. -/
theorem memberRaw_stored {d n : ℕ} (m : Operation (Fin d))
    (W : StoredCode d n) (target : Tuple (Fin d) n) :
    memberRaw d (fun a b c => m (a,b,c)) (storedState W target) =
      MaltsevWitness.member m W.toCode target := by
  unfold memberRaw
  rw [reconstructRaw_stored]
  simp only [storedState,word_length]
  unfold MaltsevWitness.member
  cases h : MaltsevWitness.reconstructTo m W.toCode target n with
  | none => simp [maybeWord]
  | some result =>
    simp only [maybeWord,Option.toList_some,List.map_singleton,List.length_singleton,
      List.headD_cons,word_length,decide_true,Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [prefixEqual_word]
    simp only [decide_eq_true_eq]
    constructor
    · intro hp
      exact view_injective hp.eq
    · intro he
      subst result
      exact PrefixEq.refl _ _

/-- The actual FP raw program decides membership when its literal stored
witness satisfies the proved semantic witness specification. -/
theorem memberRaw_correct_stored {d n : ℕ} {R : Set (Fin n → Fin d)}
    {m : Operation (Fin d)} (hm : IsMaltsev m) (hR : Preserves m R)
    (W : StoredCode d n) (hW : MaltsevWitness.Correct W.toCode R)
    (target : Tuple (Fin d) n) :
    memberRaw d (fun a b c => m (a,b,c)) (storedState W target) = true ↔ view target ∈ R := by
  rw [memberRaw_stored]
  exact MaltsevWitness.member_correct hm hR hW target

end ComplexCSP.ComplexityWitnessEncoding
