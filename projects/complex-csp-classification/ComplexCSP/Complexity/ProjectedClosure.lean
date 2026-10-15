import ComplexCSP.Complexity.TypeCache
import ComplexCSP.Complexity.WitnessEncoding
import ComplexCSP.Structure.MaltsevProjectedClosure
import PlanarHom.ZeroOneVerifierPrimitives

set_option backward.isDefEq.respectTransparency false

/-! # Actual fixed-projection closure machines

Projection scopes are runtime index lists, and witness tuples are runtime words.
The closure fuel is a fixed d^r for each fixed language arity, never d^n for the
input variable count. Compression preserves the exact last representative used
by the mathematical constructor.
-/
namespace ComplexCSP.ComplexityProjectedClosure
open MaltsevWitness MaltsevRelations ComplexityWitnessPrimitives ComplexityWitnessEncoding
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ListFlattenMachines PlanarHom.ArithmeticCircuitPrimitives

abbrev Rows := List (List ℕ)
abbrev rowsCode : BitEncoding Rows := wordCode.list

/-- Repeated scope positions remain repeated coordinates. -/
def project (scope row : List ℕ) : List ℕ := scope.map (fun i => row.getD i 0)

theorem fp_project : FP (wordCode.prod wordCode) wordCode (fun p => project p.1 p.2) := by
  have h := ListContextMachines.fp_mapWithContext wordCode BitEncoding.nat BitEncoding.nat
    (fun p => p.1.getD p.2 0) (fp_getD BitEncoding.nat 0)
  exact (((fp_snd wordCode wordCode).pair (fp_fst wordCode wordCode)).comp h)

def keys (scope : List ℕ) (rows : Rows) : Rows := rows.map (project scope)

theorem fp_keys : FP (wordCode.prod rowsCode) rowsCode (fun p => keys p.1 p.2) :=
  ListContextMachines.fp_mapWithContext wordCode wordCode wordCode _ fp_project

def prependNew (scope : List ℕ) (rows : Rows) (row : List ℕ) : Rows :=
  if project scope row ∈ keys scope rows then rows else row::rows

theorem fp_prependNew : FP ((wordCode.prod rowsCode).prod wordCode) rowsCode
    (fun p => prependNew p.1.1 p.1.2 p.2) := by
  have hstate := fp_fst (wordCode.prod rowsCode) wordCode
  have hs := hstate.comp (fp_fst wordCode rowsCode)
  have hrows := hstate.comp (fp_snd wordCode rowsCode)
  have hr := fp_snd (wordCode.prod rowsCode) wordCode
  have hk := (hs.pair hr).comp fp_project
  have hks := (hs.pair hrows).comp fp_keys
  have hm := (hk.pair hks).comp (ComplexityTypeCache.fp_member wordCode)
  have hm' : FP ((wordCode.prod rowsCode).prod wordCode) BitEncoding.bool
      (fun p => decide (project p.1.1 p.2 ∈ keys p.1.1 p.1.2)) :=
    hm.congr (fun _ => by simp)
  exact hm'.ite hrows ((hr.pair hrows).comp (ListMutationMachines.fp_cons wordCode))

def compressStep (state : List ℕ × Rows) (row : List ℕ) : List ℕ × Rows :=
  (state.1,prependNew state.1 state.2 row)

theorem fp_compressStep : FP ((wordCode.prod rowsCode).prod wordCode)
    (wordCode.prod rowsCode) (fun p => compressStep p.1 p.2) :=
  ((fp_fst (wordCode.prod rowsCode) wordCode).comp (fp_fst wordCode rowsCode)).pair fp_prependNew

private theorem fold_prepend_sublist (scope : List ℕ) (acc xs : Rows) :
    (xs.foldl (prependNew scope) acc).Sublist (xs.reverse ++ acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons,List.reverse_cons,List.append_assoc,List.singleton_append]
    apply (ih (prependNew scope acc a)).trans
    apply List.Sublist.append_left
    unfold prependNew
    split
    · exact List.sublist_cons_self _ _
    · exact List.Sublist.refl _

private theorem fold_compressStep (state : List ℕ × Rows) (xs : Rows) :
    xs.foldl compressStep state = (state.1,xs.foldl (prependNew state.1) state.2) := by
  induction xs generalizing state with
  | nil => rfl
  | cons a xs ih => exact ih (compressStep state a)

theorem compress_prefix_bound (state : List ℕ × Rows) (xs : Rows) (i : ℕ) :
    ((wordCode.prod rowsCode).encode ((xs.take i).foldl compressStep state)).length ≤
      (Polynomial.C 3*Polynomial.X+1).eval (((wordCode.prod rowsCode).prod rowsCode).encode (state,xs)).length := by
  have hp := ListDedupMachines.payloadSize_sublist wordCode (fold_prepend_sublist state.1 state.2 (xs.take i))
  rw [payloadSize_append] at hp
  have hr : payloadSize wordCode (xs.take i).reverse = payloadSize wordCode (xs.take i) := by
    simp [payloadSize_eq,List.map_reverse]
  rw [hr] at hp
  have ht := ListFilterMachines.payloadSize_take_le wordCode xs i
  have ha := payloadSize_le_word wordCode state.2
  have hx := payloadSize_le_word wordCode xs
  have hw := word_length_le_payload wordCode ((xs.take i).foldl (prependNew state.1) state.2)
  rw [fold_compressStep]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_one,BitEncoding.prod_length]
  simp only [rowsCode] at *
  omega

def compressRows (scope : List ℕ) (rows : Rows) : Rows :=
  rows.reverse.foldl (prependNew scope) []

theorem compressRows_eq (scope : List ℕ) (rows : Rows) :
    compressRows scope rows = MaltsevWitness.compress (project scope) rows := by
  unfold compressRows
  rw [List.foldl_reverse]
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    rw [List.foldr_cons,ih,MaltsevWitness.compress]
    simp only [prependNew,keys,List.contains_iff_mem]

theorem fp_compressRows : FP (wordCode.prod rowsCode) rowsCode (fun p => compressRows p.1 p.2) := by
  have hf := ListFoldMachines.fp_foldl wordCode (wordCode.prod rowsCode) compressStep fp_compressStep
    (Polynomial.C 3*Polynomial.X+1) (fun state xs i _ => compress_prefix_bound state xs i)
  have hs := fp_fst wordCode rowsCode
  have hr := fp_snd wordCode rowsCode
  have hi := (hs.pair (fp_const (wordCode.prod rowsCode) rowsCode [])).pair
    (hr.comp (ListReverseMachines.fp_reverse wordCode))
  exact (((hi.comp hf).comp (fp_snd wordCode rowsCode))).congr (fun p => by
    simp only [Function.comp_apply,fold_compressStep,compressRows])

def tripleRows (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d) (rows : Rows) : Rows :=
  rows.flatMap fun x => rows.flatMap fun y => rows.map fun z => mapOperation d m x y z

theorem fp_tripleRows (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d) :
    FP rowsCode rowsCode (tripleRows d m) := by
  let pair := wordCode.prod wordCode
  have hp := fp_fst pair wordCode
  have hx := hp.comp (fp_fst wordCode wordCode)
  have hy := hp.comp (fp_snd wordCode wordCode)
  have hz := fp_snd pair wordCode
  have hbody := (hx.pair (hy.pair hz)).comp (fp_mapOperation d m)
  have hinner := ListContextMachines.fp_mapWithContext pair wordCode wordCode _ hbody
  let ctx := rowsCode.prod wordCode
  have hc := fp_fst ctx wordCode
  have hrows := hc.comp (fp_fst rowsCode wordCode)
  have hx' := hc.comp (fp_snd rowsCode wordCode)
  have hy' := fp_snd ctx wordCode
  have hinner' := ((hx'.pair hy').pair hrows).comp hinner
  have hmiddle := (ListContextMachines.fp_mapWithContext ctx wordCode rowsCode _ hinner').comp
    (ListFlattenMachines.fp_flatten wordCode)
  have hrows' := fp_fst rowsCode wordCode
  have hx'' := fp_snd rowsCode wordCode
  have hmiddle' := ((hrows'.pair hx'').pair hrows').comp hmiddle
  have houter := (ListContextMachines.fp_mapWithContext rowsCode wordCode rowsCode _ hmiddle').comp
    (ListFlattenMachines.fp_flatten wordCode)
  exact (((fp_id rowsCode).pair (fp_id rowsCode)).comp houter).congr (fun _ => by
    simp only [Function.comp_apply,List.flatMap_def,tripleRows,id_eq])

def included (xs ys : Rows) : Bool := xs.all (fun x => decide (x ∈ ys))

theorem fp_included : FP (rowsCode.prod rowsCode) BitEncoding.bool (fun p => included p.1 p.2) := by
  have hm := ((fp_snd rowsCode wordCode).pair (fp_fst rowsCode wordCode)).comp
    (ComplexityTypeCache.fp_member wordCode)
  have hm' : FP (rowsCode.prod wordCode) BitEncoding.bool (fun p => decide (p.2 ∈ p.1)) :=
    hm.congr (fun _ => by simp)
  have ha := ZeroOneSharpPMembership.fp_allContext rowsCode wordCode _ hm'
  exact (((fp_snd rowsCode rowsCode).pair (fp_fst rowsCode rowsCode)).comp ha)

def sameKeys (scope : List ℕ) (xs ys : Rows) : Bool :=
  included (keys scope xs) (keys scope ys) && included (keys scope ys) (keys scope xs)

theorem fp_sameKeys : FP (wordCode.prod (rowsCode.prod rowsCode)) BitEncoding.bool
    (fun p => sameKeys p.1 p.2.1 p.2.2) := by
  have hs := fp_fst wordCode (rowsCode.prod rowsCode)
  have hp := fp_snd wordCode (rowsCode.prod rowsCode)
  have hx := (hs.pair (hp.comp (fp_fst rowsCode rowsCode))).comp fp_keys
  have hy := (hs.pair (hp.comp (fp_snd rowsCode rowsCode))).comp fp_keys
  exact (((hx.pair hy).comp fp_included).pair ((hy.pair hx).comp fp_included)).comp
    (fp_bool_gate (fun p => p.1 && p.2))

theorem sameKeys_correct (scope : List ℕ) (xs ys : Rows) :
    sameKeys scope xs ys = true ↔ (keys scope xs).toFinset = (keys scope ys).toFinset := by
  simp only [sameKeys,Bool.and_eq_true,included,List.all_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨hxy,hyx⟩
    apply Finset.ext
    intro a
    simp only [List.mem_toFinset]
    exact ⟨hxy a,hyx a⟩
  · intro h
    constructor <;> intro a ha
    · exact List.mem_toFinset.mp (h ▸ List.mem_toFinset.mpr ha)
    · exact List.mem_toFinset.mp (h.symm ▸ List.mem_toFinset.mpr ha)

def closureStep (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d)
    (scope : List ℕ) (rows : Rows) : Rows :=
  compressRows scope (rows ++ tripleRows d m rows)

theorem fp_closureStep (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d) :
    FP (wordCode.prod rowsCode) rowsCode (fun p => closureStep d m p.1 p.2) := by
  have hs := fp_fst wordCode rowsCode
  have hr := fp_snd wordCode rowsCode
  have ht := hr.comp (fp_tripleRows d m)
  have hnew := (hr.pair ht).comp (ListMutationMachines.fp_append wordCode)
  exact (hs.pair hnew).comp fp_compressRows

def saturate (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d) (scope : List ℕ) : ℕ → Rows → Rows
  | 0, rows => rows
  | fuel+1, rows =>
    let next := closureStep d m scope rows
    if sameKeys scope next rows then rows else saturate d m scope fuel next

/-- Fuel is a fixed program constant. Arbitrary input word sizes remain charged. -/
theorem fp_saturate (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d) (fuel : ℕ) :
    FP (wordCode.prod rowsCode) rowsCode (fun p => saturate d m p.1 fuel p.2) := by
  induction fuel with
  | zero => exact fp_snd wordCode rowsCode
  | succ fuel ih =>
    have hs := fp_fst wordCode rowsCode
    have hr := fp_snd wordCode rowsCode
    have hn := fp_closureStep d m
    have ht := (hs.pair (hn.pair hr)).comp fp_sameKeys
    have ht' : FP (wordCode.prod rowsCode) BitEncoding.bool
        (fun p => decide (sameKeys p.1 (closureStep d m p.1 p.2) p.2 = true)) :=
      ht.congr (fun _ => by simp)
    exact ht'.ite hr ((hs.pair hn).comp ih)

def projectedClosure (d r : ℕ) (m : Fin d → Fin d → Fin d → Fin d)
    (scope : List ℕ) (rows : Rows) : Rows :=
  saturate d m scope (d^r) (compressRows scope rows)

theorem fp_projectedClosure (d r : ℕ) (m : Fin d → Fin d → Fin d → Fin d) :
    FP (wordCode.prod rowsCode) rowsCode (fun p => projectedClosure d r m p.1 p.2) :=
  (((fp_fst wordCode rowsCode).pair fp_compressRows).comp (fp_saturate d m (d^r)))

end ComplexCSP.ComplexityProjectedClosure
