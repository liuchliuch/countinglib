import ComplexCSP.Complexity.SupportWitnessSemantics
import ComplexCSP.Structure.MaltsevCSPWitness

/-! # Actual FP initialization of the full-relation witness -/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityTypeStackMachines
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
variable {d : ℕ}

/-- Runtime table initialization, preserving all n isolated variable positions. -/
def fullCode (defaultValue : Fin d) (n : ℕ) : RawWitness :=
  let seed := List.replicate n defaultValue.val
  ((List.range n).map (fun i => (List.range d).map (fun a =>
    [MaltsevTypeStack.replaceAt seed i a])),[seed])

theorem fp_fullCode (defaultValue : Fin d) :
    FP BitEncoding.unaryNat witnessCode (fullCode defaultValue) := by
  have hseed := (((fp_id BitEncoding.unaryNat).pair
    (fp_const BitEncoding.unaryNat BitEncoding.nat defaultValue.val)).comp
      (RuntimePolynomialEvaluationMachines.fp_replicate BitEncoding.nat))
  have hindices := ZeroOneSharpPMembership.fp_range
  let ctxt := wordCode.prod BitEncoding.nat
  have hc := fp_fst ctxt BitEncoding.nat
  have hs := hc.comp (fp_fst wordCode BitEncoding.nat)
  have hi := hc.comp (fp_snd wordCode BitEncoding.nat)
  have ha := fp_snd ctxt BitEncoding.nat
  have hword := ((hi.pair ha).pair hs).comp fp_replaceAt
  have hsome := (hword.pair (fp_const (ctxt.prod BitEncoding.nat) maybeCode [])).comp
    (ListMutationMachines.fp_cons wordCode)
  have hrow := (((fp_id ctxt).pair (fp_const ctxt wordCode (List.range d))).comp
    (ListContextMachines.fp_mapWithContext ctxt BitEncoding.nat maybeCode _ hsome))
  have htable := (hseed.pair hindices).comp
    (ListContextMachines.fp_mapWithContext wordCode BitEncoding.nat maybeCode.list _ hrow)
  have hseedSome := (hseed.pair (fp_const BitEncoding.unaryNat maybeCode [])).comp
    (ListMutationMachines.fp_cons wordCode)
  exact htable.pair hseedSome

private theorem map_range_eq_ofFn {A : Type} (f : ℕ → A) (n : ℕ) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

/-- Full literal table/seed equality, including n=0's present empty tuple. -/
theorem fullCode_encode (defaultValue : Fin d) (n : ℕ) :
    fullCode defaultValue n = encodeCode (MaltsevWitness.fullCode defaultValue n) := by
  have hw : List.replicate n defaultValue.val = word (Vector.ofFn (fun _ : Fin n => defaultValue)) := by
    simp [word,Vector.toList_ofFn,List.ofFn_const]
  apply Prod.ext
  · simp only [fullCode,map_range_eq_ofFn]
    change List.ofFn _ = List.ofFn _
    congr 1
    funext i
    congr 1
    funext a
    rw [hw,replaceAt_word]
    simp [replaceCoordinate,view_ofFn,maybeWord,MaltsevWitness.fullCode]
  · simp [fullCode,encodeCode,MaltsevWitness.fullCode,maybeWord,hw]

end ComplexCSP.ComplexitySupportWitnessPrimitives
