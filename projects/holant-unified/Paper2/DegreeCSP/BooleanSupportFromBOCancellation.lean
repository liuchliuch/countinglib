import Paper2.DegreeCSP.GeneratedOrthogonality

/-! A finite family of two-term complex sums has one common dyadic power
with no accidental cancellation. A vanishing dyadic sum makes the next powers
equal, so no later stage can vanish unless both original terms were zero. -/
namespace Paper2.DegreeCSP.BooleanSupportFromBO
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

theorem dyadic_sum_ne_zero_after (u v : AlgebraicComplex) (n : ℕ)
    (hne : u≠0 ∨ v≠0) (hz : u^(2^n)+v^(2^n)=0)
    (m : ℕ) (hm : n<m) : u^(2^m)+v^(2^m)≠0 := by
  have hp : 2^n≠0 := ne_of_gt (pow_pos (by decide) n)
  have hu : u≠0 := by
    rcases hne with hu | hv
    · exact hu
    · intro h0
      rw [h0,zero_pow hp,zero_add] at hz
      exact hv (eq_zero_of_pow_eq_zero hz)
  have hv : v≠0 := by
    intro h0
    rw [h0,zero_pow hp,add_zero] at hz
    exact hu (eq_zero_of_pow_eq_zero hz)
  have hn : u^(2^n) = -v^(2^n) := eq_neg_of_add_eq_zero_left hz
  have he : u^(2^(n+1))=v^(2^(n+1)) := by
    rw [pow_succ,pow_mul,pow_mul,hn]
    ring
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hm)
  have he' : u^(2^(n+1+d))=v^(2^(n+1+d)) := by
    rw [pow_add,pow_mul,pow_mul,he]
  rw [he',←two_mul]
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ hv)

theorem exists_stable_power (u v : AlgebraicComplex) :
    ∃ N : ℕ,∀ m,N≤m→
      (u^(2^m)+v^(2^m)≠0 ↔ u≠0 ∨ v≠0) := by
  classical
  by_cases hne : u≠0 ∨ v≠0
  · by_cases hbad : ∃ n,u^(2^n)+v^(2^n)=0
    · obtain ⟨n,hn⟩ := hbad
      refine ⟨n+1,fun m hm=>?_⟩
      exact ⟨fun _=>hne,fun _=>dyadic_sum_ne_zero_after u v n hne hn m (by omega)⟩
    · exact ⟨0,fun m _=>⟨fun _=>hne,fun _=>not_exists.mp hbad m⟩⟩
  · have hu : u=0 := by simpa using (not_or.mp hne).1
    have hv : v=0 := by simpa using (not_or.mp hne).2
    refine ⟨0,fun m _=>?_⟩
    simp [hu,hv]

/-- One genuine power works for every row of the actual finite table. -/
theorem exists_uniform_power {X : Type} [Fintype X] (u v : X→AlgebraicComplex) :
    ∃ N : ℕ,∀ x,
      (u x^(2^N)+v x^(2^N)≠0 ↔ u x≠0 ∨ v x≠0) := by
  classical
  let threshold (x : X) := Classical.choose (exists_stable_power (u x) (v x))
  refine ⟨Finset.univ.sup threshold,fun x=>?_⟩
  apply Classical.choose_spec (exists_stable_power (u x) (v x))
  exact Finset.le_sup (f:=threshold) (Finset.mem_univ x)

end
end Paper2.DegreeCSP.BooleanSupportFromBO
