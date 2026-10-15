import Counting.Foundation.Witness
import Counting.Algorithm.KarpLuby.Guarantee

/-!
# DNF approximation and the common finite-witness count

The actual Karp–Luby program estimates the same natural-number count used by
the shared counting foundations. This bridge preserves all ambient variables,
including those absent from the formula. It adds no machine-time assumption and
does not assert a completed FPRAS implementation.
-/

namespace Counting.Adapters.KarpLuby

open Counting.Algorithm.KarpLuby
open HiddenCircuits.Approximation.SelfReduction

variable {n : Nat}

/-- The DNF finite-set denotation agrees with the common accepted-witness sum. -/
theorem modelCount_eq_countAccepted (f : DNF.Formula n) :
    DNF.modelCount f = Counting.Foundation.countAccepted (DNF.evalDNF f) := by
  rw [Counting.Foundation.countAccepted_eq_card, Fintype.card_subtype]
  rfl

/-- Interpret an ordered bit witness; the counting interface supplies length n. -/
def acceptBits (f : DNF.Formula n) (bits : List Bool) : Bool :=
  DNF.evalDNF f (fun i => bits.getD i.val false)

theorem acceptBits_ofFn (f : DNF.Formula n) (a : Fin n → Bool) :
    acceptBits f (List.ofFn a) = DNF.evalDNF f a := by
  simp [acceptBits, List.getD_eq_getElem?_getD]

/-- Exact-length Boolean witnesses count all and only satisfying assignments. -/
theorem modelCount_eq_witnessCount (f : DNF.Formula n) :
    DNF.modelCount f = Counting.Foundation.witnessCount n (acceptBits f) := by
  rw [modelCount_eq_countAccepted]
  simp only [Counting.Foundation.witnessCount, acceptBits_ofFn]

/-- The closed PAC guarantee is about the shared witness-count specification. -/
theorem run_success (f : DNF.Formula n) (epsilon delta : ℚ)
    (he : 0 < epsilon) (hd : 0 < delta) :
    1 - delta ≤ probability (fun tape : CoinTape (Program.requestedBudget f epsilon delta) =>
      |Program.run f epsilon delta tape - Counting.Foundation.witnessCount n (acceptBits f)| ≤
        epsilon * Counting.Foundation.witnessCount n (acceptBits f)) := by
  simpa only [← modelCount_eq_witnessCount f] using Program.run_success f epsilon delta he hd

/-- The actual program returns exactly zero on every tape for zero witnesses. -/
theorem run_zero (f : DNF.Formula n) (epsilon delta : ℚ)
    (h : Counting.Foundation.witnessCount n (acceptBits f) = 0)
    (tape : CoinTape (Program.requestedBudget f epsilon delta)) :
    Program.run f epsilon delta tape = 0 := by
  apply Program.run_zero f epsilon delta _ tape
  simpa only [modelCount_eq_witnessCount f] using h

end Counting.Adapters.KarpLuby
