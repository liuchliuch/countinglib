import Paper2.HeightOne.Cyclic.TwoCopyNetwork
import Paper2.HeightOne.Cyclic.BalancedCoefficients
import Paper2.HeightOne.Cyclic.ThreePairObstruction

/-! Exact coefficient rows of the actual two-copy native-X graph. The factor
four is the contribution of its two native wires in Walsh coordinates. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhaseCards Dihedral PhasePencil GroupSplit GroupSplit.MatrixGroup
open scoped BigOperators

lemma twoCopyAt_zero_sum_rows (i : Fin 3) (s : Fin 3 → AlgebraicComplex)
    (hs : ∑ j, s j = 0) :
    walshCoordinates (twoCopyAt i (balancedWalsh 0 (fun j => 4 * s j))) (fun _ => false) =
      4 * s i ^ 2 ∧
    walshCoordinates (twoCopyAt i (balancedWalsh 0 (fun j => 4 * s j)))
      (centralWord 1 (fun _ => false)) =
      4 * (-(s (nextPair i) ^ 2 + s (lastPair i) ^ 2)) ∧
    walshCoordinates (twoCopyAt i (balancedWalsh 0 (fun j => 4 * s j)))
      (flipAll (centralWord 1 (fun _ => false))) =
      4 * (-(s (nextPair i) ^ 2 + s (lastPair i) ^ 2)) ∧
    walshCoordinates (twoCopyAt i (balancedWalsh 0 (fun j => 4 * s j))) (fun _ => true) =
      4 * s i ^ 2 := by
  have hs2 : s 2 = -(s 0 + s 1) := by
    simp only [Fin.sum_univ_three] at hs
    linear_combination hs
  fin_cases i <;> refine ⟨?_,?_,?_,?_⟩
  all_goals rw [balancedWalsh_eq_coefficients,walshCoordinates_eq_coordinateAction]
  all_goals simp [Signature.coordinateAction,sum_four_assignments,twoCopyAt,twoCopyX,
    Tensor.reindex,inverseBlockPorts,balancedCoefficients,centralWord,flipPair,flipAll,
    walshInv,walsh,Fintype.sum_bool,Fin.sum_univ_three,Fin.prod_univ_four,
    funext_iff,Fin.forall_fin_succ,nextPair,lastPair,hs2]
  all_goals ring

lemma relation_scale {N : ℕ} (c : AlgebraicComplex) {a b d e : AlgebraicComplex}
    (h : Relation N a b d e) : Relation N (c * a) (c * b) (c * d) (c * e) := by
  obtain ⟨r,hr,h | h | h⟩ := h
  · refine ⟨r,hr,Or.inl ⟨?_,?_⟩⟩
    · linear_combination c * h.1
    · linear_combination c * h.2
  · refine ⟨r,hr,Or.inr (Or.inl ⟨?_,?_,?_⟩)⟩
    · rw [h.1,mul_zero]
    · rw [h.2.1,mul_zero]
    · linear_combination c * h.2.2
  · refine ⟨r,hr,Or.inr (Or.inr ⟨?_,?_,?_⟩)⟩
    · rw [h.1,mul_zero]
    · rw [h.2.1,mul_zero]
    · linear_combination c * h.2.2

lemma relation_scale_iff {N : ℕ} {c : AlgebraicComplex} (hc : c ≠ 0)
    (a b d e : AlgebraicComplex) :
    Relation N (c * a) (c * b) (c * d) (c * e) ↔ Relation N a b d e := by
  constructor
  · intro h
    have hi := relation_scale c⁻¹ h
    simpa only [← mul_assoc,inv_mul_cancel₀ hc,one_mul] using hi
  · exact relation_scale c

/-- An actual four-port signature in the safe odd-cyclic group cannot have
three nonzero balanced Walsh pairs whose scalar sum is zero. No unproved
hardness outcome or table-realizability oracle appears in this obstruction. -/
theorem actual_zero_sum_three_pairs_impossible (P : Paper1PhasePencilAccepted)
    {F : SignatureFamily AlgebraicComplex} {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (hG : GroupSplit.actualClasses F = GroupSplit.cyclicPhaseClasses N)
    (hsafe : GroupSplit.AllBinariesSafe F)
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable F f)
    (c : AlgebraicComplex) (hc : c ≠ 0) (s : Fin 3 → AlgebraicComplex)
    (hnz : ∀ i, s i ≠ 0) (hs : ∑ i, s i = 0)
    (hw : walshCoordinates f = fun x => c * balancedWalsh 0 s x) : False := by
  have hnative : f = fun x => c * balancedWalsh 0 (fun i => 4 * s i) x := by
    rw [← walsh_action_cancel f,hw,action_scalar,inverseWalsh_zero_sum s hs]
  obtain ⟨i,hi⟩ := zero_sum_three_pairs_obstruction hodd s hnz
    (by simpa only [Fin.sum_univ_three] using hs)
  let G := twoCopyAt i f
  have hreal : NetworkRealizable F G := twoCopyAt_realizable i f hf
  have hrow := (actual_cyclic_quaternary_relations P hN hG hsafe G hreal 1).1
  have hGw : walshCoordinates G = fun x => c ^ 2 *
      walshCoordinates (twoCopyAt i (balancedWalsh 0 (fun j => 4 * s j))) x := by
    dsimp only [G,twoCopyAt]
    rw [hnative]
    change walshCoordinates (twoCopyX (fun x => c *
      Tensor.reindex (blockPorts i).symm (balancedWalsh 0 (fun j => 4 * s j)) x)) = _
    rw [twoCopyX_scalar]
    exact action_scalar walshInv (c ^ 2) _
  obtain ⟨h0,hx,hy,h1⟩ := twoCopyAt_zero_sum_rows i s hs
  rw [hGw] at hrow
  simp only [h0,hx,hy,h1] at hrow
  have hrow' : Relation N ((c ^ 2 * 4) * s i ^ 2)
      ((c ^ 2 * 4) * (-(s (nextPair i) ^ 2 + s (lastPair i) ^ 2)))
      ((c ^ 2 * 4) * (-(s (nextPair i) ^ 2 + s (lastPair i) ^ 2)))
      ((c ^ 2 * 4) * s i ^ 2) := by simpa only [mul_assoc] using hrow
  exact hi ((relation_scale_iff (mul_ne_zero (pow_ne_zero 2 hc) (by norm_num)) _ _ _ _).mp hrow')

end
end Paper2.HeightOne.Cyclic
