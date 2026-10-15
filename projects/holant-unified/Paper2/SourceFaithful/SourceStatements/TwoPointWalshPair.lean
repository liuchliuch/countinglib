import Paper2.SourceFaithful.SourceStatements.TwoPointWalshPairCharacters
import Paper2.RelativeEO.GramNetwork
import Paper2.NetworkSubstitution

/-! The source's two-copy reduction of a complementary Walsh pair. The graph
has two original vertices, four ordered external ports, and one literal native
X edge joining each corresponding remaining port. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace Paper2.SourceFaithful.SourceStatements.TwoPointWalshPair
noncomputable section
open Paper2.Tractable Paper2.HeightOne.PhaseCards Paper2.RelativeEO EndpointSelfLoop
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

private theorem first_ne_second : (0 : Fin (n+2)) ≠ 1 := by
  intro h
  have h' := congrArg Fin.val h
  norm_num at h'

abbrev Tail (n : ℕ) := Remaining (0 : Fin (n+2)) 1

def pair (f : Signature AlgebraicComplex (n+2)) : Signature AlgebraicComplex 4 :=
  gramTable 0 1 first_ne_second f

theorem pair_realizable {F : SignatureFamily AlgebraicComplex}
    (f : Signature AlgebraicComplex (n+2)) (hf : NetworkRealizable F f) :
    NetworkRealizable F (pair f) := by
  have h := NetworkRealizable.substitute (F := F)
    (gramFinite 0 1 first_ne_second f).toNetwork (fun _ => rfl) (fun _ => hf)
  rw [gramFinite_denote] at h
  exact h

def tailWord (a : Fin (n+2) → Bool) : Fin n → Bool :=
  fun i => a ⟨i.val+2,by omega⟩

def tailScalar (a : Fin (n+2) → Bool) : AlgebraicComplex :=
  (2 : AlgebraicComplex)^n * sign (tailWord a)

theorem tailScalar_ne_zero (a : Fin (n+2) → Bool) : tailScalar a ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (by norm_num)) (sign_ne_zero _)

def tailWeight (a : Fin (n+2) → Bool) : ℕ := ∑ i : Fin n, if tailWord a i then 1 else 0

theorem tailScalar_weight (a : Fin (n+2) → Bool) :
    tailScalar a = (2 : AlgebraicComplex)^n * (-1)^tailWeight a := by
  unfold tailScalar sign tailWeight
  congr 1
  calc
    _ = ∏ i : Fin n, (-1 : AlgebraicComplex) ^ (if tailWord a i then 1 else 0) := by
      apply Finset.prod_congr rfl
      intro i _
      cases tailWord a i <;> simp
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

private def tailEquiv : Fin n ≃ Tail n where
  toFun i := ⟨⟨i.val+2,by omega⟩,by intro h; have := congrArg Fin.val h; simp at this,
    by intro h; have := congrArg Fin.val h; simp at this⟩
  invFun i := ⟨i.val.val-2,by
    have h0 := i.property.1
    have h1 := i.property.2
    have hn := i.val.isLt
    have h0' : i.val.val ≠ 0 := by intro h; apply h0; exact Fin.ext h
    have h1' : i.val.val ≠ 1 := by intro h; apply h1; exact Fin.ext h
    omega⟩
  left_inv := by intro i; apply Fin.ext; simp
  right_inv := by
    intro i
    apply Subtype.ext
    apply Fin.ext
    have h0 := i.property.1
    have h1 := i.property.2
    have h0' : i.val.val ≠ 0 := by intro h; apply h0; exact Fin.ext h
    have h1' : i.val.val ≠ 1 := by intro h; apply h1; exact Fin.ext h
    simp only
    omega

private theorem tail_card : Fintype.card (Tail n) = n := by
  simpa only [Fintype.card_fin] using (Fintype.card_congr (tailEquiv (n := n))).symm

private theorem tail_sign (a : Fin (n+2) → Bool) :
    sign (fun i : Tail n => a i.val) = sign (tailWord a) := by
  exact (tailEquiv.prod_comp (fun i : Tail n => if a i.val then -1 else (1 : AlgebraicComplex))).symm

private theorem character_fill (a : Fin (n+2) → Bool) (b c : Bool) (z : Tail n → Bool) :
    character a (fillPair 0 1 first_ne_second b c z) =
      character (fun i : Tail n => a i.val) z * walsh b (a 0) * walsh c (a 1) := by
  classical
  have h := (splitPorts (0 : Fin (n+2)) 1 first_ne_second).symm.prod_comp
    (fun i => walsh (fillPair 0 1 first_ne_second b c z i) (a i))
  simpa [character,splitPorts,Fintype.prod_sum_type,Fintype.prod_bool,
    fillPair_first,fillPair_second,fillPair_other,mul_comm,mul_left_comm,mul_assoc] using h.symm

private theorem native_pair_formula (f : Signature AlgebraicComplex (n+2))
    (a : Fin (n+2) → Bool) (c0 c1 : AlgebraicComplex)
    (h0 : a 0 = false) (h1 : a 1 = false) (hn : 0 < n) (he : Even n)
    (hf : f = fun x => c0 * character a x + c1 * character (fun i => !(a i)) x) :
    pair f = fun x => tailScalar a *
      (c0^2 * character (fun _ : Fin 4 => false) x +
        c1^2 * character (fun _ : Fin 4 => true) x) := by
  classical
  let A : Tail n → Bool := fun i => a i.val
  let B : Tail n → Bool := fun i => !(a i.val)
  have hAB : A ≠ B := by
    intro h
    have h' := congrFun h (tailEquiv ⟨0,hn⟩)
    change a _ = !(a _) at h'
    cases a (tailEquiv ⟨0,hn⟩).val <;> simp_all
  have hS : sign B = sign A := by
    rw [show B = (fun i => !(A i)) from rfl,sign_complement,tail_card,he.neg_one_pow,one_mul]
  have hAA := sum_character_mul A A
  have hBB := sum_character_mul B B
  have hAB' := sum_character_mul A B
  simp only [ite_eq_left,tail_card] at hAA hBB
  rw [ite_eq_right hAB] at hAB'
  have hfill0 (b c : Bool) (z : Tail n → Bool) :
      character a (fillPair 0 1 first_ne_second b c z) = character A z := by
    rw [character_fill,h0,h1]
    simp [walsh]
    rfl
  have hfill1 (b c : Bool) (z : Tail n → Bool) :
      character (fun i => !(a i)) (fillPair 0 1 first_ne_second b c z) =
        character B z * (walsh b true * walsh c true) := by
    rw [character_fill,h0,h1]
    simp only [Bool.not_false]
    exact mul_assoc _ _ _
  funext x
  let H : AlgebraicComplex := walsh (x 0) true * walsh (x 1) true
  let J : AlgebraicComplex := walsh (x 2) true * walsh (x 3) true
  have hchar0 : character (fun _ : Fin 4 => false) x = 1 := by simp [character,walsh]
  have hchar1 : character (fun _ : Fin 4 => true) x = H * J := by
    simp only [character,Fin.prod_univ_four,H,J]
    ring
  rw [hchar0,hchar1]
  change (∑ z : Tail n → Bool,
    f (fillPair 0 1 first_ne_second (x 0) (x 1) z) *
      f (fillPair 0 1 first_ne_second (x 2) (x 3) (fun i => !(z i)))) = _
  simp only [hf,hfill0,hfill1]
  change (∑ z, (c0 * character A z + c1 * (character B z * H)) *
    (c0 * character A (fun i => !(z i)) + c1 * (character B (fun i => !(z i)) * J))) = _
  simp only [character_complement,hS]
  calc
    _ = sign A * c0^2 * (∑ z, character A z * character A z) +
        sign A * c0*c1*(H+J) * (∑ z, character A z * character B z) +
        sign A * c1^2*H*J * (∑ z, character B z * character B z) := by
      simp only [Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by
      rw [hAA,hBB,hAB']
      change _ = (2 : AlgebraicComplex)^n * sign (tailWord a) * _
      rw [show sign A = sign (tailWord a) from tail_sign a]
      ring

/-- Two actual copies of the source table reduce a complementary Walsh pair
to four ports. The exact factor from all native-X wires is retained. -/
theorem pair_walsh (f : Signature AlgebraicComplex (n+2))
    (a : Fin (n+2) → Bool) (c0 c1 : AlgebraicComplex)
    (h0 : a 0 = false) (h1 : a 1 = false) (hn : 0 < n) (he : Even n)
    (hform : walshCoordinates f = fun x => c0 * delta a x + c1 * delta (fun i => !(a i)) x) :
    walshCoordinates (pair f) = fun x => tailScalar a *
      (c0^2 * delta (fun _ : Fin 4 => false) x + c1^2 * delta (fun _ : Fin 4 => true) x) := by
  have hf : f = fun x => c0 * character a x + c1 * character (fun i => !(a i)) x := by
    rw [← walsh_action_cancel f,hform,action_linear,action_delta,action_delta]
  have h := native_pair_formula f a c0 c1 h0 h1 hn he hf
  have haction : pair f = action walsh (fun x =>
      (tailScalar a * c0^2) * delta (fun _ : Fin 4 => false) x +
      (tailScalar a * c1^2) * delta (fun _ : Fin 4 => true) x) := by
    rw [h,action_linear,action_delta,action_delta]
    funext x
    ring
  rw [haction,walsh_inv_action_cancel]
  funext x
  ring

end
end Paper2.SourceFaithful.SourceStatements.TwoPointWalshPair

