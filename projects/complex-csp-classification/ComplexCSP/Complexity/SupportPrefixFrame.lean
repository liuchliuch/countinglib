import ComplexCSP.Complexity.SupportWitnessSemantics
import ComplexCSP.Complexity.WitnessSizeBounds
import PlanarHom.RestrictedListFoldMachines

/-! # Reachable-state polynomial pin/drop prefix iteration

The fold body is an actual raw FP machine. The restricted-start codec preserves
literal input words, and the restriction is proved by the constructors using
this routine; it is not a runtime validation or size oracle.
-/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityWitnessSizeBounds ComplexityEncodingBounds ComplexityProjectedClosure
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.MachineComposition

abbrev PrefixState := List ℕ × RawWitness
abbrev prefixStateCode : BitEncoding PrefixState := wordCode.prod witnessCode
variable (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d)

def prefixStep (state : PrefixState) (a : ℕ) : PrefixState :=
  (state.1 ++ [a],pinDrop d m (state.2,a))

theorem fp_prefixStep : FP (prefixStateCode.prod BitEncoding.nat) prefixStateCode
    (fun p => prefixStep d m p.1 p.2) := by
  have hs := fp_fst prefixStateCode BitEncoding.nat
  have hp := hs.comp (fp_fst wordCode witnessCode)
  have hW := hs.comp (fp_snd wordCode witnessCode)
  have ha := fp_snd prefixStateCode BitEncoding.nat
  have hsingle := (ha.pair (fp_const (prefixStateCode.prod BitEncoding.nat) wordCode [])).comp
    (ListMutationMachines.fp_cons BitEncoding.nat)
  exact ((hp.pair hsingle).comp (ListMutationMachines.fp_append BitEncoding.nat)).pair
    ((hW.pair ha).comp (fp_pinDrop d m))

theorem fold_prefix_fst (state : PrefixState) (xs : List ℕ) :
    (xs.foldl (prefixStep d m) state).1 = state.1 ++ xs := by
  induction xs generalizing state with
  | nil => simp
  | cons a xs ih => simpa [List.foldl_cons,prefixStep,List.append_assoc] using ih (prefixStep d m state a)

private def emptyCode (n : ℕ) : Code (Fin d) n where
  seed := none
  lookup _ _ := none

private theorem pinDrop_zero (W : Code (Fin d) 0) (a : ℕ) :
    pinDrop d m (encodeCode W,a) = encodeCode (emptyCode d 0) := by
  simp [pinDrop,encodeCode,tableLookup,emptyCode,List.getD_eq_getElem?_getD,maybeWord]

/-- Pin/drop retains a genuine finite-domain stored shape, even at dimension
zero. This is a syntactic shape statement, not a relational correctness premise. -/
theorem pinDrop_shape {n : ℕ} (W : Code (Fin d) n) (a : Fin d) :
    ∃ k ≤ n, ∃ U : Code (Fin d) k, pinDrop d m (encodeCode W,a.val) = encodeCode U := by
  cases n with
  | zero => exact ⟨0,le_rfl,emptyCode d 0,pinDrop_zero d m W a.val⟩
  | succ n =>
    exact ⟨n,Nat.le_succ n,pinDropCode (fun p => m p.1 p.2.1 p.2.2) W a,
      pinDrop_encodeCode (fun p => m p.1 p.2.1 p.2.2) W a⟩

theorem fold_prefix_shape {n : ℕ} (W : Code (Fin d) n) (pre xs : List ℕ)
    (hx : ∀ a ∈ xs, a < d) :
    ∃ k ≤ n, ∃ U : Code (Fin d) k,
      (xs.foldl (prefixStep d m) (pre,encodeCode W)).2 = encodeCode U := by
  induction xs generalizing n pre with
  | nil => exact ⟨n,le_rfl,W,rfl⟩
  | cons a xs ih =>
    obtain ⟨k,hk,U,hU⟩ := pinDrop_shape d m W ⟨a,hx a (by simp)⟩
    obtain ⟨j,hj,V,hV⟩ := ih U (pre++[a]) (fun b hb => hx b (by simp [hb]))
    refine ⟨j,hj.trans hk,V,?_⟩
    simpa only [List.foldl_cons,prefixStep,hU] using hV

/-- The input word is exactly an initial raw state plus finite color list. -/
def PreparedPrefix (p : PrefixState × List ℕ) : Prop :=
  p.1.1 = [] ∧ ∃ n : ℕ, ∃ W : Code (Fin d) n,
    p.1.2 = encodeCode W ∧ p.2.length ≤ n ∧ ∀ a ∈ p.2, a < d

noncomputable def preparedPrefixCode : BitEncoding {p : PrefixState × List ℕ // PreparedPrefix d p} :=
  (prefixStateCode.prod wordCode).restrict (PreparedPrefix d)

noncomputable def prefixPolynomial : Polynomial ℕ :=
  Polynomial.C 2*(Polynomial.C (6*d+3)*Polynomial.X+1)+storedPolynomial d+1

private theorem encodeCode_bound {n : ℕ} (W : Code (Fin d) n) :
    (witnessCode.encode (encodeCode W)).length ≤ (storedPolynomial d).eval n := by
  rw [encodeCode_store]
  exact stored_code_bound (storeCode W)

/-- The materialized table's literal row-list alone pays for its dimension. -/
private theorem dimension_le_code {n : ℕ} (W : Code (Fin d) n) :
    n ≤ (witnessCode.encode (encodeCode W)).length := by
  have h := BitEncoding.list_length_le maybeCode.list (encodeCode W).1
  rw [encodeCode_table_length] at h
  change n ≤ (tableCode.encode (encodeCode W).1).length at h
  rw [BitEncoding.prod_length]
  omega

/-- Every reachable accumulator is polynomial in the original prepared input.
The proof uses the actual shape preserved by the compiled pin/drop operation. -/
theorem prefix_fold_bound (p : {p : PrefixState × List ℕ // PreparedPrefix d p}) (i : ℕ) :
    (prefixStateCode.encode ((p.val.2.take i).foldl (prefixStep d m) p.val.1)).length ≤
      (prefixPolynomial d).eval ((preparedPrefixCode d).encode p).length := by
  rcases p with ⟨⟨⟨pre,Wraw⟩,xs⟩,hp⟩
  change (prefixStateCode.encode ((xs.take i).foldl (prefixStep d m) (pre,Wraw))).length ≤
    (prefixPolynomial d).eval ((prefixStateCode.prod wordCode).encode ((pre,Wraw),xs)).length
  obtain ⟨rfl,n,W,rfl,hlen,hcolors⟩ := hp
  dsimp only at hlen hcolors
  let N := ((prefixStateCode.prod wordCode).encode (([],encodeCode W),xs)).length
  have hnN : n ≤ N := by
    have h := dimension_le_code d W
    rw [BitEncoding.prod_length] at h
    dsimp only [N]
    simp only [BitEncoding.prod_length]
    omega
  obtain ⟨k,hk,U,hU⟩ := fold_prefix_shape d m W [] (xs.take i)
    (fun a ha => hcolors a (List.mem_of_mem_take ha))
  have hf := fold_prefix_fst d m ([],encodeCode W) (xs.take i)
  simp only [List.nil_append] at hf
  have hpre := encoded_list_le BitEncoding.nat (xs.take i) d (by
    intro a ha
    exact (encodeNat_length_le a).trans (hcolors a (List.mem_of_mem_take ha)).le)
  have htake : (xs.take i).length ≤ n := by
    rw [List.length_take]
    exact (Nat.min_le_right _ _).trans hlen
  have hw := (encodeCode_bound d U).trans (natPolynomial_monotone (storedPolynomial d) hk)
  rw [BitEncoding.prod_length,hf,hU]
  change 2*(wordCode.encode (xs.take i)).length+(witnessCode.encode (encodeCode U)).length+1 ≤
    (prefixPolynomial d).eval N
  have hpN := natPolynomial_monotone (prefixPolynomial d) hnN
  apply le_trans ?_ hpN
  simp only [prefixPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one]
  change 2*(BitEncoding.nat.list.encode (xs.take i)).length+_+1 ≤ _
  nlinarith

/-- The actual fold machine is reused on the honestly encoded reachable starts. -/
theorem fp_prefixFold : FP (preparedPrefixCode d) prefixStateCode
    (fun p => p.val.2.foldl (prefixStep d m) p.val.1) := by
  exact ⟨ListFoldMachines.computerOn (preparedPrefixCode d) BitEncoding.nat prefixStateCode
    (prefixStep d m) (fun p => p.val.1) (fun p => p.val.2) (fun _ => rfl)
    (Classical.choice (fp_prefixStep d m)) (prefixPolynomial d) (fun p i _ => prefix_fold_bound d m p i)⟩

/-- Bounded take by reversal and the already compiled dynamic drop machine.
Large binary prefix lengths never trigger a unary expansion. -/
theorem fp_takeWord : FP (wordCode.prod PlanarHom.Complexity.BitEncoding.nat) wordCode
    (fun p => p.1.take p.2) := by
  have hx := fp_fst wordCode BitEncoding.nat
  have hk := fp_snd wordCode BitEncoding.nat
  have hlen := hx.comp (ListCodecMachines.fp_length BitEncoding.nat)
  have hremaining := (hlen.pair hk).comp BinaryArithmetic.fp_subtraction
  have hrev := hx.comp (ListReverseMachines.fp_reverse BitEncoding.nat)
  have hout := ((hremaining.pair hrev).comp (ListDropMachines.fp_drop BitEncoding.nat 0)).comp
    (ListReverseMachines.fp_reverse BitEncoding.nat)
  apply hout.congr
  intro p
  simp only [Function.comp_apply,List.drop_reverse,List.reverse_reverse]
  by_cases h : p.2 ≤ p.1.length
  · rw [Nat.sub_sub_self h]
  · have hh : p.1.length ≤ p.2 := by omega
    simp [Nat.sub_eq_zero_of_le hh,List.take_of_length_le hh]

abbrev PrefixInput := RawWitness × (List ℕ × ℕ)
abbrev prefixInputCode : BitEncoding PrefixInput := witnessCode.prod (wordCode.prod BitEncoding.nat)

def PrefixInputValid (p : PrefixInput) : Prop :=
  ∃ n : ℕ, ∃ W : Code (Fin d) n,
    p.1 = encodeCode W ∧ p.2.1.length ≤ n ∧ ∀ a ∈ p.2.1, a < d

noncomputable def validPrefixInputCode : BitEncoding {p : PrefixInput // PrefixInputValid d p} :=
  prefixInputCode.restrict (PrefixInputValid d)

def preparePrefix (p : {p : PrefixInput // PrefixInputValid d p}) :
    {p : PrefixState × List ℕ // PreparedPrefix d p} :=
  ⟨(([],p.val.1),p.val.2.1.take p.val.2.2),by
    obtain ⟨n,W,hW,hlen,hcol⟩ := p.property
    refine ⟨rfl,n,W,hW,?_,?_⟩
    · exact (List.length_take_le' _ _).trans hlen
    · intro a ha
      exact hcol a (List.mem_of_mem_take ha)⟩

theorem fp_preparePrefix : FP (validPrefixInputCode d) (preparedPrefixCode d) (preparePrefix d) := by
  have hview : FP (validPrefixInputCode d) prefixInputCode (fun p => p.val) :=
    fp_code_view _ _ _ (fun _ => rfl)
  have hW := hview.comp (fp_fst witnessCode (wordCode.prod BitEncoding.nat))
  have hp := hview.comp (fp_snd witnessCode (wordCode.prod BitEncoding.nat))
  have htake := hp.comp fp_takeWord
  have hprepared := ((fp_const (validPrefixInputCode d) wordCode []).pair hW).pair htake
  exact hprepared.transportOutput (fun _ => rfl)

def frameRows (state : PrefixState) : Rows := (storedRows state.2).map (fun row => state.1++row)

theorem fp_frameRows : FP prefixStateCode rowsCode frameRows := by
  have hp := fp_fst wordCode witnessCode
  have hr := (fp_snd wordCode witnessCode).comp fp_storedRows
  exact (hp.pair hr).comp (ListContextMachines.fp_mapWithContext wordCode wordCode wordCode
    (fun p => p.1++p.2) (ListMutationMachines.fp_append BitEncoding.nat))

def prefixFrame (p : PrefixInput) : Rows :=
  frameRows ((p.2.1.take p.2.2).foldl (prefixStep d m) ([],p.1))

/-- Genuine FP prefix-frame computation on the reachable encoded witness shapes.
The caller supplies actual constructor outputs, not an evaluator or size oracle. -/
theorem fp_prefixFrame : FP (validPrefixInputCode d) rowsCode
    (fun p => prefixFrame d m p.val) := by
  exact (((fp_preparePrefix d).comp (fp_prefixFold d m)).comp fp_frameRows)

end ComplexCSP.ComplexitySupportWitnessPrimitives
