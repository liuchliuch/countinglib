import ComplexCSP.Complexity.CSPAssignmentVerifier
import ComplexCSP.Complexity.WitnessPrimitives
import ComplexCSP.Complexity.WitnessEncoding

/-! # Actual FP base products on natural-label assignment words

The fixed language/domain/basis are program constants. The variable input is the
literal raw CSP code together with a materialized list of natural color labels.
Two actual indexed lookups per fixed scope position replace any evaluator oracle.
-/
namespace ComplexCSP.ComplexityCSPWordAssignment
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives
open ComplexityCSPCode
open ComplexityCSPAssignmentVerifier (TableEntry allEntries mem_allEntries scope_getD)
open ComplexityWitnessPrimitives (wordCode fp_getD)

variable {q s : ℕ} {K : Type} (L : Language (Fin q) K (Fin s))

/-- Literal finite natural labels of a total assignment. -/
def assignmentLabels (g : Code) (σ : Fin g.vertices → Fin q) : List ℕ :=
  List.ofFn (fun v => (σ v).val)

@[simp] theorem assignmentLabels_getD (g : Code) (σ : Fin g.vertices → Fin q)
    (v : Fin g.vertices) : (assignmentLabels g σ).getD v.val 0 = (σ v).val := by
  simp [assignmentLabels,List.getD_eq_getElem?_getD,v.isLt]

/-- A fixed entry is recognized by actual ordered scope and word lookups. -/
def entryTest (t : TableEntry L) (p : List ℕ × (ℕ × List ℕ)) : Bool :=
  decide (p.2.1 = t.1.val) && decide (p.2.2.length = L.arity t.1) &&
    decide (∀ j, p.1.getD (p.2.2.getD j.val 0) 0 = (t.2 j).val)

theorem entryTest_true (t : TableEntry L) (w : List ℕ) (c : ℕ × List ℕ) :
    entryTest L t (w,c) = true ↔ c.1 = t.1.val ∧ c.2.length = L.arity t.1 ∧
      ∀ j, w.getD (c.2.getD j.val 0) 0 = (t.2 j).val := by
  simp [entryTest,Bool.and_eq_true,and_assoc]

theorem fp_entryTest (t : TableEntry L) :
    FP (wordCode.prod constraintEncoding) BitEncoding.bool (entryTest L t) := by
  let e := wordCode.prod constraintEncoding
  have hw := fp_fst wordCode constraintEncoding
  have hc := fp_snd wordCode constraintEncoding
  have hs := hc.comp (fp_fst BitEncoding.nat BitEncoding.nat.list)
  have hscope := hc.comp (fp_snd BitEncoding.nat BitEncoding.nat.list)
  have hsym := (hs.pair (fp_const e BitEncoding.nat t.1.val)).comp NatListSumMachines.fp_equal
  have hlen := ((hscope.comp (ListCodecMachines.fp_length BitEncoding.nat)).pair
    (fp_const e BitEncoding.nat (L.arity t.1))).comp NatListSumMachines.fp_equal
  have hj (j : Fin (L.arity t.1)) : FP e BitEncoding.bool
      (fun p => decide (p.1.getD (p.2.2.getD j.val 0) 0 = (t.2 j).val)) := by
    have hv := (hscope.pair (fp_const e BitEncoding.nat j.val)).comp (fp_getD BitEncoding.nat 0)
    have hcolor := (hw.pair hv).comp (fp_getD BitEncoding.nat 0)
    exact (hcolor.pair (fp_const e BitEncoding.nat (t.2 j).val)).comp NatListSumMachines.fp_equal
  have hall := FiniteRationalCircuits.fp_all e Finset.univ
    (fun p j => decide (p.1.getD (p.2.2.getD j.val 0) 0 = (t.2 j).val)) hj
  exact ((((hsym.pair hlen).comp (fp_bool_gate (fun p => p.1 && p.2))).pair hall).comp
    (fp_bool_gate (fun p => p.1 && p.2))).congr (fun p => by simp [entryTest])

/-- Fixed finite table lookup; malformed unmatched inputs receive the unit. -/
def lookupWeight [One K] : List (TableEntry L) → List ℕ × (ℕ × List ℕ) → K
  | [], _ => 1
  | t::ts,p => if entryTest L t p then L.value t.1 t.2 else lookupWeight ts p

def constraintWeight [One K] (w : List ℕ) (c : ℕ × List ℕ) : K :=
  lookupWeight L (allEntries L) (w,c)

def assignmentWeight [Monoid K] (g : Code) (w : List ℕ) : K :=
  (g.constraints.map (constraintWeight L w)).prod

section Machines
variable [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

theorem fp_lookupWeight (ts : List (TableEntry L)) :
    FP (wordCode.prod constraintEncoding) (numberFieldEncoding basis) (lookupWeight L ts) := by
  induction ts with
  | nil => exact fp_const _ _ 1
  | cons t ts ih =>
    have ht := (fp_entryTest L t).congr
      (fun p => show entryTest L t p = decide (entryTest L t p = true) by simp)
    exact ht.ite (fp_const _ _ (L.value t.1 t.2)) ih

theorem fp_constraintWeight : FP (wordCode.prod constraintEncoding) (numberFieldEncoding basis)
    (fun p => constraintWeight L p.1 p.2) := fp_lookupWeight L basis (allEntries L)

/-- Genuine polynomial-time ComputeF base product on materialized natural labels. -/
theorem fp_assignmentWeight : FP (encoding.prod wordCode) (numberFieldEncoding basis)
    (fun p => assignmentWeight L p.1 p.2) := by
  have hg := fp_fst encoding wordCode
  have hw := fp_snd encoding wordCode
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hc := (hg.comp hv).comp (fp_snd BitEncoding.unaryNat constraintEncoding.list)
  have hm := (hw.pair hc).comp (ListContextMachines.fp_mapWithContext
    wordCode constraintEncoding (numberFieldEncoding basis)
    (fun p => constraintWeight L p.1 p.2) (fp_constraintWeight L basis))
  exact hm.comp (MaterializedFieldListMachines.fp_product basis)
end Machines

section Semantics
variable [One K]

theorem lookupWeight_eq (ts : List (TableEntry L)) (p : List ℕ × (ℕ × List ℕ)) (z : K)
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
      rw [lookupWeight, ite_eq_right ht]
      exact ih hex' (fun u hu => hall u (List.mem_cons_of_mem _ hu))

theorem constraintWeight_eq (g : Code) (σ : Fin g.vertices → Fin q)
    (c : ℕ × List ℕ) (hc : ConstraintValid L g.vertices c) :
    constraintWeight L (assignmentLabels g σ) c = entryValue L (constraintEntry L g σ c) := by
  let t : TableEntry L := ⟨⟨c.1,hc.choose⟩,σ ∘ scope L g c hc⟩
  have ht : entryTest L t (assignmentLabels g σ,c) = true := by
    apply (entryTest_true L t _ c).mpr
    refine ⟨rfl,hc.choose_spec.1,fun j => ?_⟩
    rw [scope_getD L g c hc j,assignmentLabels_getD]
    rfl
  have hsame (u : TableEntry L) (hu : entryTest L u (assignmentLabels g σ,c) = true) : u = t := by
    obtain ⟨hs,hl,hm⟩ := (entryTest_true L u _ c).mp hu
    rcases u with ⟨i,a⟩
    have hi : i = ⟨c.1,hc.choose⟩ := Fin.ext hs.symm
    subst i
    have ha : a = σ ∘ scope L g c hc := by
      funext j
      have hmj := hm j
      rw [scope_getD L g c hc j,assignmentLabels_getD] at hmj
      exact Fin.ext hmj.symm
    subst a
    rfl
  have he := lookupWeight_eq L (allEntries L) (assignmentLabels g σ,c) (L.value t.1 t.2)
    ⟨t,mem_allEntries L t,ht⟩ (fun u _ hu => by rw [hsame u hu])
  simpa [constraintWeight,constraintEntry,hc,entryValue,t] using he
end Semantics

theorem assignmentWeight_eq [CommMonoid K] (g : Code) (hg : Valid L g)
    (σ : Fin g.vertices → Fin q) :
    assignmentWeight L g (List.ofFn (fun v => (σ v).val)) = eval L g σ := by
  unfold assignmentWeight eval assignmentWord
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c hc
  exact constraintWeight_eq L g σ c (hg c hc)

/-- The same concrete word convention used by materialized witness reconstruction. -/
theorem assignmentLabels_tuple (g : Code) (x : MaltsevWitness.Tuple (Fin q) g.vertices) :
    assignmentLabels g (MaltsevWitness.view x) = ComplexityWitnessEncoding.word x := by
  apply List.ext_getElem
  · simp [assignmentLabels,ComplexityWitnessEncoding.word]
  · intro i hi hj
    simp [assignmentLabels,ComplexityWitnessEncoding.word,MaltsevWitness.view]

/-- Typed ComputeF bridge for an actual stored witness tuple. -/
theorem assignmentWeight_tuple_eq [CommMonoid K] (g : Code) (hg : Valid L g)
    (x : MaltsevWitness.Tuple (Fin q) g.vertices) :
    assignmentWeight L g (ComplexityWitnessEncoding.word x) = eval L g (MaltsevWitness.view x) := by
  rw [← assignmentLabels_tuple g x]
  exact assignmentWeight_eq L g hg (MaltsevWitness.view x)

end ComplexCSP.ComplexityCSPWordAssignment
