import Paper2.MatchingPropagation
import Paper2.CommonPhase.Recovery

/-! EO reconstruction from the actual pair contractions avoiding two fixed
ports. This is an independent algebraic input to the high-height argument. -/
namespace Paper2.HighHeightReconstruction
open CommonPhase EndpointSelfLoop MatchingPropagation
variable {ι : Type}

/-- The zero-loop triangle requires only its three displayed loops. -/
theorem coefficient_zero_of_selected_three [DecidableEq ι]
    (F : Tensor ℂ ι) (x : ι → Bool) (a b c : ι)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : x a = true) (hb : x b = true) (hc : x c = false)
    (hzab : loop a b hab F = 0) (hzac : loop a c hac F = 0)
    (hzbc : loop b c hbc F = 0) : F x = 0 := by
  by_contra hnz
  let y : ι → Bool := fun i => x (Equiv.swap a c i)
  let z : ι → Bool := fun i => x (Equiv.swap b c i)
  have hxac : x c = !(x a) := by simp [ha,hc]
  have hxbc : x c = !(x b) := by simp [hb,hc]
  have hyab : y b = !(y a) := by
    simp [y,Equiv.swap_apply_of_ne_of_ne hab.symm hbc,hb,hc]
  have hswap : (fun i => y (Equiv.swap a b i)) = z :=
    swap_triangle x a b c hab hac hbc ha hb hc
  have hxy : F x + F y = 0 := by
    simpa only [loop_apply_restrict a c hac F x hxac,Pi.zero_apply] using
      congrFun hzac (restrict a c x)
  have hxz : F x + F z = 0 := by
    simpa only [loop_apply_restrict b c hbc F x hxbc,Pi.zero_apply] using
      congrFun hzbc (restrict b c x)
  have hyz : F y + F z = 0 := by
    simpa only [loop_apply_restrict a b hab F y hyab,hswap,Pi.zero_apply] using
      congrFun hzab (restrict a b y)
  rcases triangle_nonzero (by norm_num : (2:ℂ) ≠ 0) (F x) (F y) (F z) hnz with h | h | h
  · exact h hxy
  · exact h hxz
  · exact h hyz

/-- At least two occupied and two unoccupied ports remain after excluding a
fixed pair from any balanced word on at least eight ports. -/
theorem exists_triangle_away [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (e : PortPair ι) (x : ι → Bool) (hx : doubledCharge x = 0) :
    ∃ (a b c : Remaining e.first e.second), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      x a.val = true ∧ x b.val = true ∧ x c.val = false := by
  classical
  have hw : 4 ≤ weight x := by unfold doubledCharge at hx; omega
  have hw' : 4 ≤ weight (fun i => !(x i)) := by
    have := weight_complement_add x
    unfold doubledCharge at hx
    omega
  let T : Finset ι := Finset.univ.filter (fun i => x i = true)
  let Z : Finset ι := Finset.univ.filter (fun i => x i = false)
  have hT : T.card = weight x := by simp only [T,Finset.card_filter,weight]
  have hZ : Z.card = weight (fun i => !(x i)) := by
    simp only [Z,Finset.card_filter,weight]
    apply Finset.sum_congr rfl
    intro i hi
    simp
  have hTc : 1 < (T \ pairPorts e).card := by
    have h₁ := Finset.card_sdiff_add_card_inter T (pairPorts e)
    have h₂ := Finset.card_le_card (Finset.inter_subset_right (s₁ := T) (s₂ := pairPorts e))
    simp only [card_pairPorts] at h₂
    omega
  have hZc : 0 < (Z \ pairPorts e).card := by
    have h₁ := Finset.card_sdiff_add_card_inter Z (pairPorts e)
    have h₂ := Finset.card_le_card (Finset.inter_subset_right (s₁ := Z) (s₂ := pairPorts e))
    simp only [card_pairPorts] at h₂
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hTc
  obtain ⟨c,hc⟩ := Finset.card_pos.mp hZc
  have ha' : a ≠ e.first ∧ a ≠ e.second := by simpa using (Finset.mem_sdiff.mp ha).2
  have hb' : b ≠ e.first ∧ b ≠ e.second := by simpa using (Finset.mem_sdiff.mp hb).2
  have hc' : c ≠ e.first ∧ c ≠ e.second := by simpa using (Finset.mem_sdiff.mp hc).2
  have hat : x a = true := (Finset.mem_filter.mp (Finset.mem_sdiff.mp ha).1).2
  have hbt : x b = true := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hb).1).2
  have hcf : x c = false := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hc).1).2
  refine ⟨⟨a,ha'⟩,⟨b,hb'⟩,⟨c,hc'⟩,?_,?_,?_,hat,hbt,hcf⟩
  · exact fun h => hab (congrArg Subtype.val h)
  · intro h
    have hv := congrArg Subtype.val h
    simp only at hv
    rw [hv,hcf] at hat
    contradiction
  · intro h
    have hv := congrArg Subtype.val h
    simp only at hv
    rw [hv,hcf] at hbt
    contradiction

/-- The subdeck avoiding one fixed pair is already injective on EO tensors of
arity at least eight. All zero equations refer to actual native-X sums. -/
theorem eo_zero_of_away_contractions [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (e : PortPair ι) (F : Tensor ℂ ι) (heo : Tensor.ChargeLayer F 0)
    (hz : ∀ r : PortPair ι, r.Disjoint e → contraction F r = 0) : F = 0 := by
  classical
  funext x
  change F x = 0
  by_contra hx
  obtain ⟨a,b,c,hab,hac,hbc,ha,hb,hc⟩ := exists_triangle_away hn e x (heo x hx)
  have hab' : a.val ≠ b.val := fun h => hab (Subtype.ext h)
  have hac' : a.val ≠ c.val := fun h => hac (Subtype.ext h)
  have hbc' : b.val ≠ c.val := fun h => hbc (Subtype.ext h)
  exact hx (coefficient_zero_of_selected_three F x a.val b.val c.val hab' hac' hbc' ha hb hc
    (hz ⟨a.val,b.val,hab'⟩ ⟨a.property.1,a.property.2,b.property.1,b.property.2⟩)
    (hz ⟨a.val,c.val,hac'⟩ ⟨a.property.1,a.property.2,c.property.1,c.property.2⟩)
    (hz ⟨b.val,c.val,hbc'⟩ ⟨b.property.1,b.property.2,c.property.1,c.property.2⟩))

theorem eo_eq_of_away_contractions [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (e : PortPair ι) (F G : Tensor ℂ ι)
    (hF : Tensor.ChargeLayer F 0) (hG : Tensor.ChargeLayer G 0)
    (he : ∀ r : PortPair ι, r.Disjoint e → contraction F r = contraction G r) : F = G := by
  apply sub_eq_zero.mp
  apply eo_zero_of_away_contractions hn e (F-G) (chargeLayer_sub F G 0 hF hG)
  intro r hr
  rw [contraction,loop_sub]
  change contraction F r - contraction G r = 0
  rw [he r hr,sub_self]

end Paper2.HighHeightReconstruction
