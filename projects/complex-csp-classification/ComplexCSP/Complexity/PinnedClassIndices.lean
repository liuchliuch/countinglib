import ComplexCSP.Complexity.PinnedLayerPrimitives
import PlanarHom.RestrictedIterationMachine

/-! # Charged unary coordinate enumeration

Both the loop count and every emitted coordinate have unary encodings. This is
an actual quadratic-output enumerator, never a total binary-to-unary conversion.
-/
namespace ComplexCSP.ComplexityPinnedLayer
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityEncodingBounds

def appendLength (xs : List ℕ) : List ℕ := xs ++ [xs.length]

theorem fp_appendLength : FP BitEncoding.unaryNat.list BitEncoding.unaryNat.list appendLength := by
  have hn := ListUnaryLengthMachine.fp_length BitEncoding.unaryNat
  have hsingle := (hn.pair (fp_const BitEncoding.unaryNat.list BitEncoding.unaryNat.list [])).comp
    (ListMutationMachines.fp_cons BitEncoding.unaryNat)
  exact ((fp_id BitEncoding.unaryNat.list).pair hsingle).comp
    (ListMutationMachines.fp_append BitEncoding.unaryNat)

theorem appendLength_iterate (n : ℕ) : appendLength^[n] [] = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Function.iterate_succ_apply',ih,appendLength,List.range_succ]

/-- Fixed polynomial output bound on every intermediate iterator state. -/
theorem unaryRange_bound (n i : ℕ) (hi : i ≤ n) :
    (BitEncoding.unaryNat.list.encode (appendLength^[i] [])).length ≤
      (Polynomial.C 6*Polynomial.X^2+Polynomial.C 3*Polynomial.X+1).eval n := by
  rw [appendLength_iterate]
  have h := encoded_list_le BitEncoding.unaryNat (List.range i) n (by
    intro a ha
    simpa only [BitEncoding.unaryNat_length] using (List.mem_range.mp ha).le.trans hi)
  simp only [List.length_range] at h
  have h' := h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (6*n+3) hi) 1)
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X,Polynomial.eval_one] using
      h'.trans (by nlinarith : (6*n+3)*n+1 ≤ 6*n^2+3*n+1)

theorem fp_unaryRange : FP BitEncoding.unaryNat BitEncoding.unaryNat.list List.range := by
  obtain ⟨body⟩ := fp_appendLength
  exact (show FP BitEncoding.unaryNat BitEncoding.unaryNat.list (fun n => appendLength^[n] []) from
    ⟨BoundedIterationMachine.fromSeedComputer BitEncoding.unaryNat.list appendLength [] body
      (Polynomial.C 6*Polynomial.X^2+Polynomial.C 3*Polynomial.X+1) unaryRange_bound⟩).congr
        appendLength_iterate

end ComplexCSP.ComplexityPinnedLayer
