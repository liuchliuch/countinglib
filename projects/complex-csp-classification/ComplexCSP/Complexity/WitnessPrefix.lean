import ComplexCSP.Complexity.WitnessEncoding
import PlanarHom.ZeroOneVerifierPrimitives

/-! # Runtime prefix comparison for materialized witness reconstruction -/
namespace ComplexCSP.ComplexityWitnessPrimitives
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives

/-- Only coordinates present in the first word are tested. On equally sized
valid tuple words this is exactly the mathematical prefix relation. -/
def prefixEqual (k : ℕ) (xs ys : List ℕ) : Bool :=
  xs.zipIdx.all (fun p => if p.2 < k then decide (p.1 = ys.getD p.2 0) else true)

theorem fp_prefixEqual :
    FP (BitEncoding.nat.prod (wordCode.prod wordCode)) BitEncoding.bool
      (fun p => prefixEqual p.1 p.2.1 p.2.2) := by
  let ec := BitEncoding.nat.prod wordCode
  let ei := BitEncoding.nat.prod BitEncoding.nat
  have hc := fp_fst ec ei
  have hk := hc.comp (fp_fst BitEncoding.nat wordCode)
  have hy := hc.comp (fp_snd BitEncoding.nat wordCode)
  have hp := fp_snd ec ei
  have hx := hp.comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hi := hp.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hv := (hy.pair hi).comp (fp_getD BitEncoding.nat 0)
  have heq := (hx.pair hv).comp NatListSumMachines.fp_equal
  have ht := (hi.pair hk).comp BinaryArithmetic.fp_comparison
  have hbody := ht.ite heq (fp_const (ec.prod ei) BitEncoding.bool true)
  have hl := fp_snd BitEncoding.nat (wordCode.prod wordCode)
  have hleft := hl.comp (fp_fst wordCode wordCode)
  have hright := hl.comp (fp_snd wordCode wordCode)
  have hcontext := (fp_fst BitEncoding.nat (wordCode.prod wordCode)).pair hright
  have hindexed := hleft.comp (ListIndexMachines.fp_zipIdx BitEncoding.nat)
  exact (hcontext.pair hindexed).comp
    (ZeroOneSharpPMembership.fp_allContext ec ei _ hbody)

end ComplexCSP.ComplexityWitnessPrimitives

namespace ComplexCSP.ComplexityWitnessEncoding
open MaltsevWitness MaltsevRelations ComplexityWitnessPrimitives

/-- Exact proof/implementation link, with no restriction on k or dimension. -/
theorem prefixEqual_word {d n : ℕ} (k : ℕ) (x y : Tuple (Fin d) n) :
    prefixEqual k (word x) (word y) = true ↔ PrefixEq k (view x) (view y) := by
  rw [prefixEqual, List.all_eq_true, List.forall_mem_zipIdx]
  constructor
  · intro h i hi
    have hin : i.val < (word x).length := by simp
    have hp := h i.val hin
    simp only [Nat.zero_add, hi, ↓reduceIte, decide_eq_true_eq] at hp
    apply Fin.ext
    simpa [word, view, List.getD_eq_getElem?_getD] using hp
  · intro h i hi
    have hin : i < n := by simpa using hi
    dsimp only
    by_cases hik : i < k
    · simp only [Nat.zero_add, hik, ↓reduceIte, decide_eq_true_eq]
      rw [word_getD y ⟨i,hin⟩]
      have hp := congrArg Fin.val (h ⟨i,hin⟩ hik)
      simpa [word, view] using hp
    · simp [hik]

end ComplexCSP.ComplexityWitnessEncoding
