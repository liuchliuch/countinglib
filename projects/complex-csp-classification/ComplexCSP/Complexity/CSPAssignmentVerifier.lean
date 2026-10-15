import ComplexCSP.Complexity.CSPCode
import PlanarHom.ZeroOneVerifierMachines
import PlanarHom.MaterializedFieldListMachines
import Mathlib.Logic.Equiv.Finset
import Mathlib.Logic.Encodable.Pi

set_option backward.isDefEq.respectTransparency false

/-! # Actual fixed-language assignment-weight verification machines

Colors use canonical one-hot blocks. A fixed finite table-entry list is compiled
into finite control; every constraint occurrence is evaluated by actual dynamic
scope lookup and exact field multiplication. No FP verifier is an assumption.
-/
namespace ComplexCSP.ComplexityCSPAssignmentVerifier
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives
open PlanarHom.ZeroOneSharpPMembership ComplexityCSPCode

variable {q s : ℕ} {K : Type} (L : Language (Fin q) K (Fin s))

abbrev TableEntry := (i : Fin s) × (Fin (L.arity i) → Fin q)

def allEntries : List (TableEntry L) :=
  List.ofFn ((Encodable.fintypeEquivFin (α := TableEntry L)).symm)

theorem mem_allEntries (t : TableEntry L) : t ∈ allEntries L := by
  unfold allEntries
  apply List.mem_ofFn.mpr
  exact ⟨Encodable.fintypeEquivFin t, Equiv.symm_apply_apply _ t⟩

/-- Executable finite one-hot check; the machine theorem is inherited from the
proved equivalent fixed-control PLGH checker. -/
def rowMatchCode (q : ℕ) (w : Bits) (v : ℕ) (c : Fin q) : Bool :=
  decide (∀ j : Fin q, getBit w (q*v+j.val) = decide (c=j))

 theorem rowMatchCode_eq (q : ℕ) (w : Bits) (v : ℕ) (c : Fin q) :
    rowMatchCode q w v c = rowMatch q w v c := by
  simp [rowMatchCode,rowMatch,Matches]

/-- Compare one fixed target table entry with the actual occurrence scope. -/
def entryTest (t : TableEntry L) (p : Bits × (ℕ × List ℕ)) : Bool :=
  decide (p.2.1 = t.1.val) && decide (p.2.2.length = L.arity t.1) &&
    decide (∀ j, rowMatchCode q p.1 (p.2.2.getD j.val 0) (t.2 j) = true)

 theorem entryTest_true (t : TableEntry L) (w : Bits) (c : ℕ × List ℕ) :
    entryTest L t (w,c) = true ↔ c.1 = t.1.val ∧ c.2.length = L.arity t.1 ∧
      ∀ j, Matches q w (c.2.getD j.val 0) (t.2 j) := by
  simp [entryTest, Bool.and_eq_true, and_assoc, rowMatchCode,Matches]

theorem fp_entryTest (t : TableEntry L) :
    FP (BitEncoding.bits.prod constraintEncoding) BitEncoding.bool (entryTest L t) := by
  let e := BitEncoding.bits.prod constraintEncoding
  have hw := fp_fst BitEncoding.bits constraintEncoding
  have hc := fp_snd BitEncoding.bits constraintEncoding
  have hs := hc.comp (fp_fst BitEncoding.nat BitEncoding.nat.list)
  have hscope := hc.comp (fp_snd BitEncoding.nat BitEncoding.nat.list)
  have hsym := (hs.pair (fp_const e BitEncoding.nat t.1.val)).comp NatListSumMachines.fp_equal
  have hlen := ((hscope.comp (ListCodecMachines.fp_length BitEncoding.nat)).pair
    (fp_const e BitEncoding.nat (L.arity t.1))).comp NatListSumMachines.fp_equal
  have hj (j : Fin (L.arity t.1)) : FP e BitEncoding.bool
      (fun p => rowMatchCode q p.1 (p.2.2.getD j.val 0) (t.2 j)) := by
    have hv := (hscope.pair (fp_const e BitEncoding.nat j.val)).comp
      (PfaffianList.fp_at BitEncoding.nat 0)
    exact ((hw.pair hv).comp (fp_rowMatch q (t.2 j))).congr
      (fun p => (rowMatchCode_eq q p.1 (p.2.2.getD j.val 0) (t.2 j)).symm)
  have hall := FiniteRationalCircuits.fp_all e Finset.univ
    (fun p j => rowMatchCode q p.1 (p.2.2.getD j.val 0) (t.2 j)) hj
  exact ((((hsym.pair hlen).comp (fp_bool_gate (fun p => p.1 && p.2))).pair hall).comp
    (fp_bool_gate (fun p => p.1 && p.2))).congr (fun p => by simp [entryTest])

def lookupWeight [One K] : List (TableEntry L) → Bits × (ℕ × List ℕ) → K
  | [], _ => 1
  | t::ts, p => if entryTest L t p then L.value t.1 t.2 else lookupWeight ts p

def constraintWeight [One K] (w : Bits) (c : ℕ × List ℕ) : K :=
  lookupWeight L (allEntries L) (w,c)

def assignmentWeight [Monoid K] (g : Code) (w : Bits) : K :=
  (g.constraints.map (constraintWeight L w)).prod

section Machines
variable [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

theorem fp_lookupWeight (ts : List (TableEntry L)) :
    FP (BitEncoding.bits.prod constraintEncoding) (numberFieldEncoding basis) (lookupWeight L ts) := by
  induction ts with
  | nil => exact fp_const _ _ 1
  | cons t ts ih =>
      have ht := (fp_entryTest L t).congr
        (fun p => show entryTest L t p = decide (entryTest L t p = true) by simp)
      exact ht.ite (fp_const _ _ (L.value t.1 t.2)) ih

theorem fp_constraintWeight : FP (BitEncoding.bits.prod constraintEncoding)
    (numberFieldEncoding basis) (fun p => constraintWeight L p.1 p.2) :=
  fp_lookupWeight L basis (allEntries L)

theorem fp_assignmentWeight : FP (encoding.prod BitEncoding.bits)
    (numberFieldEncoding basis) (fun p => assignmentWeight L p.1 p.2) := by
  have hg := fp_fst encoding BitEncoding.bits
  have hw := fp_snd encoding BitEncoding.bits
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hc := (hg.comp hv).comp (fp_snd BitEncoding.unaryNat constraintEncoding.list)
  have hm := (hw.pair hc).comp (ListContextMachines.fp_mapWithContext
    BitEncoding.bits constraintEncoding (numberFieldEncoding basis)
    (fun p => constraintWeight L p.1 p.2) (fp_constraintWeight L basis))
  exact hm.comp (MaterializedFieldListMachines.fp_product basis)
end Machines

section Semantics
variable [One K]

theorem lookupWeight_eq (ts : List (TableEntry L)) (p : Bits × (ℕ × List ℕ)) (z : K)
    (hex : ∃ t ∈ ts, entryTest L t p = true)
    (hall : ∀ t ∈ ts, entryTest L t p = true → L.value t.1 t.2 = z) :
    lookupWeight L ts p = z := by
  induction ts with
  | nil => simp at hex
  | cons t ts ih =>
    by_cases ht : entryTest L t p = true
    · simpa only [lookupWeight,ht,ite_true] using hall t (List.mem_cons_self) ht
    · have hex' : ∃ u ∈ ts, entryTest L u p = true := by
        obtain ⟨u,hu,hm⟩ := hex
        rcases List.mem_cons.mp hu with he | hu
        · subst u; exact (ht hm).elim
        · exact ⟨u,hu,hm⟩
      simpa only [lookupWeight,ht,Bool.false_eq_true,ite_false] using ih hex'
        (fun u hu => hall u (List.mem_cons_of_mem _ hu))

omit [One K] in
 theorem scope_getD (g : Code) (c : ℕ × List ℕ) (hc : ConstraintValid L g.vertices c)
    (j : Fin (L.arity ⟨c.1,hc.choose⟩)) :
    c.2.getD j.val 0 = (scope L g c hc j).val := by
  have hj : j.val < c.2.length := lt_of_lt_of_eq j.isLt hc.choose_spec.1.symm
  simp [scope,List.getD_eq_getElem?_getD,hj]

theorem constraintWeight_eq (g : Code) (σ : Fin g.vertices → Fin q) (w : Bits)
    (hw : ∀ v, Matches q w v.val (σ v))
    (c : ℕ × List ℕ) (hc : ConstraintValid L g.vertices c) :
    constraintWeight L w c = entryValue L (constraintEntry L g σ c) := by
  let t : TableEntry L := ⟨⟨c.1,hc.choose⟩,σ ∘ scope L g c hc⟩
  have ht : entryTest L t (w,c) = true := by
    apply (entryTest_true L t w c).mpr
    refine ⟨rfl,hc.choose_spec.1,fun j => ?_⟩
    rw [scope_getD L g c hc j]
    exact hw _
  have hsame (u : TableEntry L) (hu : entryTest L u (w,c) = true) : u = t := by
    obtain ⟨hs,hl,hm⟩ := (entryTest_true L u w c).mp hu
    rcases u with ⟨i,a⟩
    have hi : i = ⟨c.1,hc.choose⟩ := Fin.ext hs.symm
    subst i
    have ha : a = σ ∘ scope L g c hc := by
      funext j
      have hmj := hm j
      rw [scope_getD L g c hc j] at hmj
      exact matches_unique hmj (hw _)
    subst a
    rfl
  have he := lookupWeight_eq L (allEntries L) (w,c) (L.value t.1 t.2)
    ⟨t,mem_allEntries L t,ht⟩ (fun u _ hu => by rw [hsame u hu])
  simpa [constraintWeight,constraintEntry,hc,entryValue,t] using he

end Semantics

 theorem assignmentWeight_eq [CommMonoid K] (g : Code) (hg : Valid L g)
    (σ : Fin g.vertices → Fin q) (w : Bits) (hw : ∀ v, Matches q w v.val (σ v)) :
    assignmentWeight L g w = eval L g σ := by
  unfold assignmentWeight eval assignmentWord
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  exact constraintWeight_eq L g σ w hw c (hg c hc)

end ComplexCSP.ComplexityCSPAssignmentVerifier
