import Counting.MatchgateWidth.Main
import Counting.MatchgateWidth.Semantics

/-!
# A downstream client of common-base compression and public partition semantics

Connection-primality supplies a width-at-most-three presentation on the same
qutrit domain and exact labelled language. The client obtains both an upper
bound for the actual minimum on any supplied instance class and preservation
of the public partition for every raw instance, including nullary vertices.
The instance class is not restricted or enlarged during this argument.
-/
namespace Counting.MatchgateWidth.Client
noncomputable section
open _root_.MatchgateWidth

/-- The positive collapse theorem yields an actual common presentation and
an upper bound for the minimum defined on the chosen class. Exact equality of
languages then preserves every public partition, without a planarity premise
on the particular instance being evaluated. -/
theorem connection_prime_partition_compression {S : LabelledShape} {t : ℕ}
    (C : LabelledInstanceClass S) (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank = 3) (hprime : AllLeftConnectionPrime p) :
    ∃ r ≤ 3, ∃ q : LabelledCommonPresentation S (Fin 3) r,
      q.left = p.left ∧ q.language = p.language ∧
      minimumExactCommonWidthOn C p.language (p.finiteWidthOn C) ≤ r ∧
      ∀ a b c (I : LabelledInstance S a b c),
        (Semantics.closedInstance I q.language).partition Empty.elim =
          (Semantics.closedInstance I p.language).partition Empty.elim := by
  obtain ⟨r, hr, H, _hH, _hRank, _hEight, q, _hFactor, hLeft, hLang, _hEquiv⟩ :=
    allLeft_connectionPrime_compression p hM hprime
  refine ⟨r, hr, q, hLeft, hLang, ?_, ?_⟩
  · apply minimumExactCommonWidthOn_le
    rw [← hLang]
    exact q.hasExactCommonWidthOn C
  · intro a b c I
    rw [hLang]

/-- The same compressed common presentation preserves all ordered open
boundary tensors in the public semantics, pointwise and at every arity. -/
theorem connection_prime_boundary_compression {S : LabelledShape} {t : ℕ}
    (p : LabelledCommonPresentation S (Fin 3) t)
    (hM : p.baseMatrix.rank = 3) (hprime : AllLeftConnectionPrime p) :
    ∃ r ≤ 3, ∃ q : LabelledCommonPresentation S (Fin 3) r,
      q.left = p.left ∧ q.language = p.language ∧
      ∀ a b c n (I : AllLeftGadget S a b c n) (z : Fin n → Fin 3),
        (Semantics.openInstance I q.language).partition z = I.value p.language z := by
  obtain ⟨r, hr, H, _hH, _hRank, _hEight, q, _hFactor, hLeft, hLang, _hEquiv⟩ :=
    allLeft_connectionPrime_compression p hM hprime
  refine ⟨r, hr, q, hLeft, hLang, ?_⟩
  intro a b c n I z
  rw [hLang, Semantics.openInstance_partition]

end
end Counting.MatchgateWidth.Client
