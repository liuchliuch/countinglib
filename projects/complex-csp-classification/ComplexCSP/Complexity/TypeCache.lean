import ComplexCSP.Complexity.EncodedEquality
import ComplexCSP.Structure.MaltsevTypeMaterialized
import PlanarHom.ListContextFilterMachines
import PlanarHom.ListReverseMachines

/-! # Literal FP label-cache operations for memoized type search

Labels have a canonical runtime encoding. Equality is an actual comparison of
those codewords. The exact last-occurrence order of Lean's List.dedup is retained,
so this interface agrees with the already proved materialized type algorithm.
-/
namespace ComplexCSP.ComplexityTypeCache
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives PlanarHom.ListFlattenMachines
variable {A : Type} [DecidableEq A]

theorem fp_member (e : BitEncoding A) :
    FP (e.prod e.list) BitEncoding.bool (fun p => decide (p.1 ∈ p.2)) := by
  apply (ListPredicateMachines.fp_member e ComplexityEncodedEquality.equal
    (ComplexityEncodedEquality.fp_equal e)).congr
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply, List.any_eq_true, ComplexityEncodedEquality.equal,
    decide_eq_true_eq]
  constructor
  · rintro ⟨a,ha,he⟩
    exact he ▸ ha
  · intro h
    exact ⟨p.1,h,rfl⟩

def prependFresh (acc : List A) (a : A) : List A := if a ∈ acc then acc else a::acc

theorem fp_prependFresh (e : BitEncoding A) :
    FP (e.list.prod e) e.list (fun p => prependFresh p.1 p.2) := by
  have hacc := fp_fst e.list e
  have ha := fp_snd e.list e
  have hm := (ha.pair hacc).comp (fp_member e)
  exact hm.ite hacc ((ha.pair hacc).comp (ListMutationMachines.fp_cons e))

theorem fold_prependFresh_sublist (acc xs : List A) :
    (xs.foldl prependFresh acc).Sublist (xs.reverse ++ acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons a xs ih =>
    rw [List.foldl_cons, List.reverse_cons, List.append_assoc, List.singleton_append]
    apply (ih (prependFresh acc a)).trans
    apply List.Sublist.append_left
    unfold prependFresh
    split
    · exact List.sublist_cons_self _ _
    · exact List.Sublist.refl _

theorem prependFresh_prefix_bound (e : BitEncoding A) (acc xs : List A) (i : ℕ) :
    (e.list.encode ((xs.take i).foldl prependFresh acc)).length ≤
      (Polynomial.C 3*Polynomial.X+1).eval ((e.list.prod e.list).encode (acc,xs)).length := by
  have hp := ListDedupMachines.payloadSize_sublist e (fold_prependFresh_sublist acc (xs.take i))
  rw [payloadSize_append] at hp
  have hr : payloadSize e (xs.take i).reverse = payloadSize e (xs.take i) := by
    simp [payloadSize_eq,List.map_reverse]
  rw [hr] at hp
  have ht := ListFilterMachines.payloadSize_take_le e xs i
  have ha := payloadSize_le_word e acc
  have hx := payloadSize_le_word e xs
  have hw := word_length_le_payload e ((xs.take i).foldl prependFresh acc)
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_one,BitEncoding.prod_length]
  omega

theorem fold_prependFresh_eq_dedup (xs : List A) :
    xs.reverse.foldl prependFresh [] = xs.dedup := by
  rw [List.foldl_reverse]
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rw [List.foldr_cons, ih, List.dedup_cons']
    rfl

/-- Actual FP exact-order deduplication, not only finite-set equivalence. -/
theorem fp_dedup (e : BitEncoding A) : FP e.list e.list (List.dedup : List A → List A) := by
  have hf := ListFoldMachines.fp_foldl e e.list prependFresh (fp_prependFresh e)
    (Polynomial.C 3*Polynomial.X+1) (fun acc xs i _ => prependFresh_prefix_bound e acc xs i)
  have hi := (fp_const e.list e.list []).pair (ListReverseMachines.fp_reverse e)
  exact (hi.comp hf).congr (fun xs => fold_prependFresh_eq_dedup xs)

abbrev Cache (A : Type) := List (ℕ × List A)
def cacheEncoding (e : BitEncoding A) : BitEncoding (Cache A) := (BitEncoding.nat.prod e.list).list

def cacheTest (query : ℕ × A) (entry : ℕ × List A) : Bool :=
  decide (entry.1 = query.1 ∧ query.2 ∈ entry.2)

def lookup (cache : Cache A) (len : ℕ) (a : A) : Bool × List A :=
  let found := cache.filter (cacheTest (len,a))
  (!(decide (found = [])), (found.headD (0,[])).2)

theorem fp_cacheTest (e : BitEncoding A) :
    FP ((BitEncoding.nat.prod e).prod (BitEncoding.nat.prod e.list)) BitEncoding.bool
      (fun p => cacheTest p.1 p.2) := by
  have hq := fp_fst (BitEncoding.nat.prod e) (BitEncoding.nat.prod e.list)
  have he := fp_snd (BitEncoding.nat.prod e) (BitEncoding.nat.prod e.list)
  have hk := hq.comp (fp_fst BitEncoding.nat e)
  have ha := hq.comp (fp_snd BitEncoding.nat e)
  have hn := he.comp (fp_fst BitEncoding.nat e.list)
  have hs := he.comp (fp_snd BitEncoding.nat e.list)
  have hlen := (hn.pair hk).comp NatListSumMachines.fp_equal
  have hmem := (ha.pair hs).comp (fp_member e)
  exact ((hlen.pair hmem).comp (fp_bool_gate (fun p => p.1 && p.2))).congr
    (fun p => by simp [cacheTest])

theorem fp_lookup (e : BitEncoding A) :
    FP ((BitEncoding.nat.prod e).prod (cacheEncoding e)) (BitEncoding.bool.prod e.list)
      (fun p => lookup p.2 p.1.1 p.1.2) := by
  let entryCode := BitEncoding.nat.prod e.list
  let inputCode := (BitEncoding.nat.prod e).prod (cacheEncoding e)
  have hf := ListContextFilterMachines.fp_filterWithContext (BitEncoding.nat.prod e) entryCode
    (fun p => cacheTest p.1 p.2) (fp_cacheTest e)
  have hlen := hf.comp (ListCodecMachines.fp_length entryCode)
  have hz := (hlen.pair (fp_const inputCode BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  have hsome := hz.comp (fp_bool_unary BitEncoding.bool not)
  have hv := (hf.comp (ListDecompositionMachines.fp_headD entryCode (0,[]))).comp
    (fp_snd BitEncoding.nat e.list)
  exact (hsome.pair hv).congr (fun p => by simp [lookup])

theorem lookup_eq_cachedTypeList (cache : Cache A) (len : ℕ) (a : A) :
    lookup cache len a = ((MaltsevWitness.cachedTypeList cache len a).isSome,
      (MaltsevWitness.cachedTypeList cache len a).getD []) := by
  have hfind : MaltsevWitness.cachedTypeList cache len a =
      (cache.filter (cacheTest (len,a))).head?.map Prod.snd := by
    rw [List.head?_filter]
    rfl
  rw [hfind]
  unfold lookup
  generalize cache.filter (cacheTest (len,a)) = found
  cases found <;> rfl

end ComplexCSP.ComplexityTypeCache
