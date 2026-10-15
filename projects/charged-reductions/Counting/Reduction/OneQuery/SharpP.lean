import Counting.Reduction.OneQuery.Compiler
import Counting.Complexity.SharpP
import PlanarHom.BinaryGcdBits

/-! # Binary answer lengths from public witness counters -/

namespace Counting.Reduction.OneQuery
open PlanarHom.Complexity Counting.Complexity

/-- Counting witnesses bounds numeral length without computing the count. This
includes the empty numeral for zero and the unique zero-length witness. -/
theorem answer_length_le {β : Type} {eb : BitEncoding β} {g : β → ℕ}
    (w : SharpPWitness eb.toFinEncoding g) (b : β) :
    (BitEncoding.nat.encode (g b)).length ≤
      (w.witnessLength + 1).eval (eb.encode b).length := by
  rw [show (BitEncoding.nat.encode (g b)).length = Nat.size (g b) from
    PlanarHom.BinaryArithmetic.encodeNat_length (g b), Polynomial.eval_add, Polynomial.eval_one]
  exact (Nat.size_le_size (w.count_le b)).trans_eq Nat.size_pow


end Counting.Reduction.OneQuery

namespace Counting.Complexity.ParsimoniousReduction
open PlanarHom.Complexity Counting.Reduction.OneQuery

/-- An actual, single-query charged compiler. The target is only assumed to
have a public polynomial witness verifier, not a polynomial counting algorithm.
Both promises contain exactly the original codecs' canonical codewords. -/
noncomputable def toCharged {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {f : α → ℕ} {g : β → ℕ}
    (r : ParsimoniousReduction ea.toFinEncoding eb.toFinEncoding f g)
    (w : SharpPWitness eb.toFinEncoding g) :
    PromisePolyTimeTuringReduction (problem ea f) (problem eb g) :=
  compile r (w.witnessLength + 1) (answer_length_le w)

end Counting.Complexity.ParsimoniousReduction
