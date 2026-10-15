import Counting.Complexity.Reduction
import PlanarHom.Complexity

/-! # Canonical encoded counting promises

Only literal codewords are promised. The decoder below specifies a total target
value; no algorithm or polynomial bound for an arbitrary decoder is assumed.
-/

namespace Counting.Reduction.OneQuery
open PlanarHom.Complexity

variable {α : Type}

/-- Keep the original faithful codewords and binary natural-number answers. -/
def problem (e : BitEncoding α) (f : α → ℕ) : PromiseProblem where
  valid raw := ∃ a, e.encode a = raw
  value := encodedFunction e BitEncoding.nat f []

theorem valid_encode (e : BitEncoding α) (f : α → ℕ) (a : α) :
    (problem e f).valid (e.encode a) := ⟨a, rfl⟩

@[simp] theorem value_encode (e : BitEncoding α) (f : α → ℕ) (a : α) :
    (problem e f).value (e.encode a) = BitEncoding.nat.encode (f a) :=
  encodedFunction_encode e BitEncoding.nat f [] a

/-- A canonical promised word has a unique typed source, not an arbitrary decode. -/
theorem canonical_unique (e : BitEncoding α) (f : α → ℕ) {raw : Bits} (h : (problem e f).valid raw) :
    ∃! a, e.encode a = raw := by
  obtain ⟨a, ha⟩ := h
  exact ⟨a, ha, fun b hb => e.injective (hb.trans ha.symm)⟩

end Counting.Reduction.OneQuery
