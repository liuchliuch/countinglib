import Counting.Algorithm.KarpLubyRequest.Preparation.Resources

/-! The finite cleanup schedule executes a pop loop on every work stack. Its
cost is the actual number of stored work bits plus one boundary transition per
fixed stack and the final state-reset/halt instruction.
-/
namespace Counting.Algorithm.KarpLubyRequest.Preparation
noncomputable section
open Turing Computability Holant.Complexity StackProtocol
open scoped BigOperators

set_option backward.isDefEq.respectTransparency false

private theorem lt_successor_eq_of_ne {a b : ℕ} (h : a ≠ b) :
    (a < b + 1) = (a < b) := propext (by omega)

private theorem cleanup_time_eq {total before after cost : ℕ}
    (hstep : after = before + cost) (hle : after ≤ total) :
    total - before + 1 = (total - after + 1) + cost := by omega

private theorem indexed_cost_bound {K L : Type} [Fintype K] [Fintype L]
    (n : ℕ) (e : Fin n ≃ K) (ι : K → L) (hι : Function.Injective ι)
    (weight : L → ℕ) :
    (∑ k : Fin n, if k.val < n then weight (ι (e k)) + 1 else 0) ≤
      (∑ l : L, weight l) + n := by
  classical
  have he : (∑ k : Fin n, if k.val < n then weight (ι (e k)) + 1 else 0) =
      (∑ k : Fin n, weight (ι (e k))) + n := by
    simp only [Fin.isLt, ite_true, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one]
  rw [e.sum_comp (fun k => weight (ι k))] at he
  have hs : (∑ k : K, weight (ι k)) ≤ ∑ l : L, weight l := by
    apply Finset.sum_le_sum_of_injOn ι
    · intro a _ b _ h; exact hι h
    · exact Finset.subset_univ _
    · intro k _; exact le_refl _
    · intro k _ _; exact Nat.zero_le _
  exact he.le.trans (Nat.add_le_add_right hs n)

def clearLocation (n : ℕ) : Label :=
  if h : n < workCount then .clear ⟨n, h⟩ else .done

def cleared (frame : Stack → List Bool) (n : ℕ) : Stack → List Bool
  | .inl k => if (workAt.symm k).val < n then [] else frame (.inl k)
  | .inr k => frame (.inr k)

def prefixCost (frame : Stack → List Bool) (n : ℕ) : ℕ :=
  ∑ k : Fin workCount, if k.val < n then (frame (.inl (workAt k))).length + 1 else 0

theorem cleared_zero (frame : Stack → List Bool) : cleared frame 0 = frame := by
  funext k
  cases k with
  | inl k => simp only [cleared, Nat.not_lt_zero, ite_false]
  | inr k => rfl

theorem cleared_at (frame : Stack → List Bool) (k : Fin workCount) :
    cleared frame k.val (.inl (workAt k)) = frame (.inl (workAt k)) := by
  change (if (workAt.symm (workAt k)).val < k.val then [] else _) = _
  rw [workAt.symm_apply_apply]
  simp only [Nat.lt_irrefl, ite_false]

theorem cleared_update (frame : Stack → List Bool) (k : Fin workCount) :
    Function.update (cleared frame k.val) (.inl (workAt k)) [] = cleared frame (k.val + 1) := by
  funext j
  cases j with
  | inr u => rfl
  | inl w =>
    by_cases h : w = workAt k
    · subst w
      simp only [Function.update_self, cleared, workAt.symm_apply_apply, Nat.lt_succ_self, ite_true]
    · have hi : workAt.symm w ≠ k := by
        intro hi
        apply h
        simpa only [workAt.apply_symm_apply] using congrArg workAt hi
      have hv : (workAt.symm w).val ≠ k.val := fun hv => hi (Fin.ext hv)
      have he := lt_successor_eq_of_ne hv
      simp only [Function.update_apply, Sum.inl.injEq, h, ite_false, cleared, he]

theorem cleared_all (frame : Stack → List Bool) :
    cleared frame workCount = ({output := frame output} : Data).tapes := by
  funext j
  cases j with
  | inr u => cases u; rfl
  | inl w =>
    have h := (workAt.symm w).isLt
    change (if (workAt.symm w).val < workCount then [] else frame (.inl w)) = _
    rw [if_pos h]
    rcases w with j | (j | (j | (j | j))) <;> rfl

theorem prefixCost_zero (frame : Stack → List Bool) : prefixCost frame 0 = 0 := by
  simp only [prefixCost, Nat.not_lt_zero, ite_false, Finset.sum_const_zero]

theorem prefixCost_mono (frame : Stack → List Bool) {a b : ℕ} (h : a ≤ b) :
    prefixCost frame a ≤ prefixCost frame b := by
  apply Finset.sum_le_sum
  intro k _
  by_cases ha : k.val < a
  · have hb : k.val < b := lt_of_lt_of_le ha h
    simp only [ha, hb, ite_true, le_refl]
  · simp only [ha, ite_false]
    exact Nat.zero_le _

theorem prefixCost_succ (frame : Stack → List Bool) (k : Fin workCount) :
    prefixCost frame (k.val + 1) =
      prefixCost frame k.val + ((frame (.inl (workAt k))).length + 1) := by
  have he (i : Fin workCount) :
      (if i.val < k.val + 1 then (frame (.inl (workAt i))).length + 1 else 0) =
      (if i.val < k.val then (frame (.inl (workAt i))).length + 1 else 0) +
        (if i = k then (frame (.inl (workAt i))).length + 1 else 0) := by
    by_cases hi : i.val < k.val
    · have hlt : i.val < k.val + 1 := Nat.lt_succ_of_lt hi
      have hne : i ≠ k := fun h => (Nat.ne_of_lt hi) (congrArg Fin.val h)
      simp only [hi, hlt, hne, ite_true, ite_false, Nat.add_zero]
    · by_cases hk : i = k
      · subst i
        simp only [Nat.lt_succ_self, Nat.lt_irrefl, ite_true, ite_false, Nat.zero_add]
      · have hv : i.val ≠ k.val := fun hv => hk (Fin.ext hv)
        have hlt : ¬ i.val < k.val + 1 := by
          rw [lt_successor_eq_of_ne hv]
          exact hi
        simp only [hi, hlt, hk, ite_false, Nat.add_zero]
  unfold prefixCost
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

/-- Every suffix of the displayed static schedule has an exact actual run. -/
theorem cleanup_suffix (frame : Stack → List Bool) (memory : Memory)
    (n : ℕ) (hn : n ≤ workCount) :
    RunsExactly computer.step (cfg (clearLocation n) memory (cleared frame n))
      (finalConfiguration (frame output))
      (prefixCost frame workCount - prefixCost frame n + 1) := by
  induction hn using Nat.decreasingInduction with
  | self =>
    have hs : computer.step (cfg .done memory (cleared frame workCount)) =
        some (finalConfiguration (frame output)) := by
      change some (⟨none, initial, cleared frame workCount⟩ : computer.Cfg) = _
      rw [cleared_all]
      rfl
    simpa only [clearLocation, Nat.lt_irrefl, ↓reduceDIte, Nat.sub_self, Nat.zero_add] using
      runsExactly_one hs
  | of_succ n hn ih =>
    let k : Fin workCount := ⟨n, hn⟩
    have hc := clear_exact computer.step (.inl (workAt k)) (.clear k) (clearNext k)
      (by intro m t; rfl) memory (cleared frame n)
    change RunsExactly computer.step
      (cfg (.clear k) memory (cleared frame k.val))
      (cfg (clearLocation (n + 1)) memory
        (Function.update (cleared frame k.val) (.inl (workAt k)) []))
      ((cleared frame k.val (.inl (workAt k))).length + 1) at hc
    rw [cleared_at, cleared_update] at hc
    have ht := prefixCost_succ frame k
    have hle := prefixCost_mono frame (show n + 1 ≤ workCount from hn)
    have hrun := hc.trans ih
    rw [clearLocation, dif_pos hn]
    have htime := cleanup_time_eq ht hle
    rw [htime]
    exact hrun

/-- Complete work cleanup and final register reset. No assertion that a work
bank is already empty is required, including after a rejected raw request. -/
theorem cleanup_run (frame : Stack → List Bool) (memory : Memory) :
    RunsExactly computer.step (cfg clearFirst memory frame)
      (finalConfiguration (frame output)) (prefixCost frame workCount + 1) := by
  have h := cleanup_suffix frame memory 0 (Nat.zero_le _)
  simpa only [clearLocation, workCount_pos, dif_pos, cleared_zero, prefixCost_zero,
    Nat.sub_zero, clearFirst] using h

set_option maxRecDepth 4096 in
theorem prefixCost_bound (frame : Stack → List Bool) :
    prefixCost frame workCount ≤ stackSize frame + workCount := by
  exact indexed_cost_bound workCount workAt (Sum.inl : WorkStack → Stack)
    (fun _ _ h => Sum.inl.inj h) (fun k => (frame k).length)

end
end Counting.Algorithm.KarpLubyRequest.Preparation
