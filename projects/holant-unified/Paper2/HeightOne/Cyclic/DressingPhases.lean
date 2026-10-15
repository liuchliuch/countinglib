import Paper2.HeightOne.PhaseCards.Cards

/-! The odd-order four-port character map is genuinely bijective on all root
phases. Its inverse records the unique square root, not an assumed dressing. -/
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable
open scoped BigOperators

lemma rootGroup_pow {N : ℕ} (s : rootsOfUnity N AlgebraicComplex) : s ^ N = 1 := by
  apply Subtype.ext
  exact ((mem_rootsOfUnity N s.val).mp s.property)

lemma odd_root_half_power {N : ℕ} (hN : Odd N) (s : rootsOfUnity N AlgebraicComplex) :
    (s ^ ((N + 1) / 2)) ^ 2 = s := by
  rw [← pow_mul]
  have hn : (N + 1) / 2 * 2 = N + 1 := by obtain ⟨k, hk⟩ := hN; omega
  rw [hn, pow_succ, rootGroup_pow, one_mul]

lemma odd_root_square_injective {N : ℕ} (hN : Odd N) :
    Function.Injective (fun s : rootsOfUnity N AlgebraicComplex => s ^ 2) := by
  intro a b he
  have ha : (a ^ 2) ^ ((N + 1) / 2) = a := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact odd_root_half_power hN a
  have hb : (b ^ 2) ^ ((N + 1) / 2) = b := by
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact odd_root_half_power hN b
  change a ^ 2 = b ^ 2 at he
  rw [← ha, ← hb, he]

def dressingMap {N : ℕ} (r : Fin 4 → rootsOfUnity N AlgebraicComplex) :
    rootsOfUnity N AlgebraicComplex × (Fin 3 → rootsOfUnity N AlgebraicComplex) :=
  (∏ i, r i, fun j => r 0 * r j.succ)

def dressingInverse {N : ℕ}
    (q : rootsOfUnity N AlgebraicComplex × (Fin 3 → rootsOfUnity N AlgebraicComplex)) :
    Fin 4 → rootsOfUnity N AlgebraicComplex :=
  let a := ((q.2 0 * q.2 1 * q.2 2) / q.1) ^ ((N + 1) / 2)
  ![a, q.2 0 / a, q.2 1 / a, q.2 2 / a]

lemma dressingMap_inverse {N : ℕ} (hN : Odd N)
    (q : rootsOfUnity N AlgebraicComplex × (Fin 3 → rootsOfUnity N AlgebraicComplex)) :
    dressingMap (dressingInverse q) = q := by
  let a := ((q.2 0 * q.2 1 * q.2 2) / q.1) ^ ((N + 1) / 2)
  have ha : a ^ 2 = (q.2 0 * q.2 1 * q.2 2) / q.1 := odd_root_half_power hN _
  apply Prod.ext
  · change (∏ i : Fin 4, (![a, q.2 0 / a, q.2 1 / a, q.2 2 / a] : Fin 4 → _) i) = q.1
    simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three]
    change a * (q.2 0 / a) * (q.2 1 / a) * (q.2 2 / a) = q.1
    apply Subtype.ext
    apply Units.ext
    have ha' := congrArg (fun z : rootsOfUnity N AlgebraicComplex => (z.val : AlgebraicComplex)) ha
    push_cast at ha' ⊢
    change (a.val : AlgebraicComplex) ^ 2 =
      (q.2 0).val * (q.2 1).val * (q.2 2).val / q.1.val at ha'
    change (a.val : AlgebraicComplex) * ((q.2 0).val / a.val) *
      ((q.2 1).val / a.val) * ((q.2 2).val / a.val) = q.1.val
    calc
      _ = ((q.2 0).val * (q.2 1).val * (q.2 2).val) / (a.val : AlgebraicComplex) ^ 2 := by
        field_simp
        <;> ring
      _ = q.1.val := by rw [ha']; field_simp
  · funext i
    fin_cases i <;> simp [dressingMap, dressingInverse, mul_div_cancel_left]

lemma dressingMap_injective {N : ℕ} (hN : Odd N) :
    Function.Injective (@dressingMap N) := by
  intro a b h
  have h0 : a 0 ^ 2 = b 0 ^ 2 := by
    have hx (r : Fin 4 → rootsOfUnity N AlgebraicComplex) :
        r 0 ^ 2 = ((dressingMap r).2 0 * (dressingMap r).2 1 * (dressingMap r).2 2) /
          (dressingMap r).1 := by
      apply Subtype.ext
      apply Units.ext
      dsimp [dressingMap]
      push_cast
      simp only [Fin.prod_univ_four]
      push_cast
      change ((r 0).val : AlgebraicComplex) ^ 2 =
        (((r 0).val : AlgebraicComplex) * (r 1).val *
          (((r 0).val : AlgebraicComplex) * (r 2).val) *
          (((r 0).val : AlgebraicComplex) * (r 3).val)) /
          (((r 0).val : AlgebraicComplex) * (r 1).val * (r 2).val * (r 3).val)
      field_simp
      <;> ring
    rw [hx a, hx b, h]
  have ha0 := odd_root_square_injective hN h0
  have hp (i : Fin 3) : a i.succ = b i.succ := by
    have he := congrArg (fun q => q.2 i) h
    change a 0 * a i.succ = b 0 * b i.succ at he
    rw [ha0] at he
    exact mul_left_cancel he
  funext i
  induction i using Fin.cases with
  | zero => exact ha0
  | succ i => exact hp i

/-- Source dressing surjectivity at odd N, with the portwise root phases
computed by the displayed inverse map. -/
theorem odd_dressing_bijective {N : ℕ} (hN : Odd N) : Function.Bijective (@dressingMap N) :=
  ⟨dressingMap_injective hN, fun q => ⟨dressingInverse q, dressingMap_inverse hN q⟩⟩

end
end Paper2.HeightOne.Cyclic
