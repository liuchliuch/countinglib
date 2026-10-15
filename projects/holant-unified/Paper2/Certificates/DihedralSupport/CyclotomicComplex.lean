import Paper2.Certificates.DihedralSupport.CyclotomicArithmetic

/-! The literal root hypothesis of Appendix A.1 over any characteristic-zero
field. In particular, the complex interfaces need no algebraicity hypothesis
on the entries of the tensor. The three labelled phases exhaust all roots
of unity of order dividing three in the ambient field. -/
namespace Paper2.Certificates.DihedralSupport.CyclotomicComplex

variable {K : Type*} [Field K] [CharZero K]

theorem cube_of_polynomial (w : K) (hw : w ^ 2 + w + 1 = 0) : w ^ 3 = 1 := by
  linear_combination (w - 1) * hw

theorem ne_one_of_polynomial (w : K) (hw : w ^ 2 + w + 1 = 0) : w ≠ 1 := by
  intro h
  subst w
  norm_num at hw

theorem primitive_of_polynomial (w : K) (hw : w ^ 2 + w + 1 = 0) :
    IsPrimitiveRoot w 3 := by
  have hc := cube_of_polynomial w hw
  have hn := ne_one_of_polynomial w hw
  have hn2 : w ^ 2 ≠ 1 := by
    intro he
    apply hn
    calc
      w = w ^ 2 * w := by rw [he,one_mul]
      _ = w ^ 3 := by ring
      _ = 1 := hc
  apply IsPrimitiveRoot.mk_of_lt w (by decide) hc
  intro n hn0 hn3
  have hn12 : n = 1 ∨ n = 2 := by omega
  rcases hn12 with rfl | rfl
  · simpa using hn
  · exact hn2

theorem polynomial_of_primitive (w : K) (hw : IsPrimitiveRoot w 3) :
    w ^ 2 + w + 1 = 0 := by
  have hf : (w - 1) * (w ^ 2 + w + 1) = 0 := by
    calc
      (w - 1) * (w ^ 2 + w + 1) = w ^ 3 - 1 := by ring
      _ = 0 := by rw [hw.pow_eq_one]; ring
  exact (mul_eq_zero.mp hf).resolve_left (sub_ne_zero.mpr (hw.ne_one (by decide)))

theorem cubic_factorization (w : K) (hw : w ^ 2 + w + 1 = 0) (z : K) :
    (z - 1) * (z - w) * (z - w ^ 2) = z ^ 3 - 1 := by
  have hc := cube_of_polynomial w hw
  linear_combination (-z ^ 2 + z) * hw + (z - 1) * hc

theorem cube_roots_complete (w : K) (hw : w ^ 2 + w + 1 = 0)
    (z : K) (hz : z ^ 3 = 1) : ∃ r : Fin 3, z = w ^ r.val := by
  have hf : (z - 1) * (z - w) * (z - w ^ 2) = 0 := by
    rw [cubic_factorization w hw,hz]
    ring
  rcases mul_eq_zero.mp hf with h | h
  · rcases mul_eq_zero.mp h with h | h
    · exact ⟨0,by simpa using sub_eq_zero.mp h⟩
    · exact ⟨1,by simpa using sub_eq_zero.mp h⟩
  · exact ⟨2,by simpa using sub_eq_zero.mp h⟩

theorem phase_injective (w : K) (hw : w ^ 2 + w + 1 = 0) :
    Function.Injective (fun r : Fin 3 => w ^ r.val) := by
  intro i j h
  exact Fin.ext ((primitive_of_polynomial w hw).pow_inj i.isLt j.isLt h)

end Paper2.Certificates.DihedralSupport.CyclotomicComplex

