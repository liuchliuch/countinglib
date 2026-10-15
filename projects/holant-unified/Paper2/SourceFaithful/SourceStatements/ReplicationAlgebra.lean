import Paper2.Synthesis.OrdinaryTransport

/-! The literal tensor contraction in the copying premise commutes with the
fixed inverse-K action. Every ordered boundary block is retained, including
blocks of size zero. -/
namespace Paper2.SourceFaithful.SourceStatements.Replication
open Paper2.Tractable
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {K : Type*} [CommSemiring K]

def coefficient {n : ℕ} (N : Kernel K) (x y : Fin n → Bool) : K :=
  ∏ i, N (x i) (y i)

theorem action_append (N : Kernel K) {r m : ℕ} (f : Signature K (r+m))
    (a : Fin r → Bool) (q : Fin m → Bool) :
    Signature.coordinateAction (fun _ => N) f (Fin.append a q) =
      ∑ u : Fin r → Bool, ∑ v : Fin m → Bool,
        coefficient N a u * coefficient N q v * f (Fin.append u v) := by
  unfold Signature.coordinateAction
  rw [← (Fin.appendEquiv r m).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  change _ * f (Fin.append u v) = _
  simp [coefficient, Fin.prod_univ_add, Fin.append_left, Fin.append_right, mul_assoc]

theorem word_orthogonal (N : Kernel K)
    (ho : ∀ u v, (∑ b : Bool, N (!b) u * N b v) = Signature.equality u v)
    {r : ℕ} (u v : Fin r → Bool) :
    (∑ a : Fin r → Bool, coefficient N (fun i => !(a i)) u * coefficient N a v) =
      if u=v then 1 else 0 := by
  simp only [coefficient, ← Finset.prod_mul_distrib]
  have hp := Fintype.prod_sum (fun i : Fin r => fun b : Bool => N (!b) (u i)*N b (v i))
  calc
    _ = ∏ i : Fin r, ∑ b : Bool, N (!b) (u i)*N b (v i) := hp.symm
    _ = _ := by simp only [ho]; exact Signature.prod_equality u v

theorem contraction_action (N : Kernel K)
    (ho : ∀ u v, (∑ b : Bool, N (!b) u * N b v) = Signature.equality u v)
    {r m : ℕ} (g : Signature K r) (f : Signature K (r+m)) (q : Fin m → Bool) :
    (∑ a : Fin r → Bool,
      Signature.coordinateAction (fun _ => N) g (fun i => !(a i)) *
      Signature.coordinateAction (fun _ => N) f (Fin.append a q)) =
    Signature.coordinateAction (fun _ => N)
      (fun w => ∑ a : Fin r → Bool, g a * f (Fin.append a w)) q := by
  simp only [action_append]
  change (∑ a, (∑ u, coefficient N (fun i => !(a i)) u * g u) *
    (∑ v, ∑ w, coefficient N a v * coefficient N q w * f (Fin.append v w))) =
    ∑ w, coefficient N q w * ∑ a, g a * f (Fin.append a w)
  calc
    _ = ∑ u : Fin r → Bool, ∑ v : Fin r → Bool, ∑ w : Fin m → Bool,
        (∑ a : Fin r → Bool, coefficient N (fun i => !(a i)) u * coefficient N a v) *
          (g u*coefficient N q w*f (Fin.append v w)) := by
      simp_rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro a _
      ac_rfl
    _ = ∑ u : Fin r → Bool, ∑ v : Fin r → Bool, ∑ w : Fin m → Bool,
        (if u=v then 1 else 0) * (g u*coefficient N q w*f (Fin.append v w)) := by
      simp_rw [word_orthogonal N ho]
    _ = ∑ u : Fin r → Bool, ∑ w : Fin m → Bool,
        g u*coefficient N q w*f (Fin.append u w) := by
      simp only [← Finset.mul_sum]
      simp
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      ac_rfl

theorem action_product (N : Kernel K) {r s : ℕ} (c : K)
    (g : Signature K r) (h : Signature K s) (p : Fin r → Bool) (y : Fin s → Bool) :
    Signature.coordinateAction (fun _ => N)
      (fun w => c*g (fun i => w (Fin.castAdd s i))*h (fun i => w (Fin.natAdd r i)))
      (Fin.append p y) =
      c * Signature.coordinateAction (fun _ => N) g p *
        Signature.coordinateAction (fun _ => N) h y := by
  rw [action_append]
  simp only [Fin.append_left, Fin.append_right]
  change (∑ u, ∑ v, coefficient N p u * coefficient N y v * (c*g u*h v)) =
    c*(∑ u, coefficient N p u*g u)*(∑ v, coefficient N y v*h v)
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ac_rfl

theorem inverseK_orthogonal (u v : Bool) :
    (∑ b : Bool, KInverse (!b) u*KInverse b v) = Signature.equality u v := by
  cases u <;> cases v <;> simp only [Fintype.sum_bool, Bool.not_false, Bool.not_true,
    KInverse, Signature.equality, ↓reduceIte]
  all_goals field_simp [sqrtTwo_ne_zero]
  all_goals ring_nf
  all_goals norm_num [sqrtTwo_sq, imaginaryUnit_sq]
  all_goals rw [show imaginaryUnit*imaginaryUnit= -1 by simpa only [pow_two] using imaginaryUnit_sq]
  all_goals ring

theorem inverseK_carrier_step {r s : ℕ} (g : Signature AlgebraicComplex r)
    (h : Signature AlgebraicComplex s) (f : Signature AlgebraicComplex (r+(r+s)))
    (c : AlgebraicComplex)
    (step : ∀ p y, (∑ a : Fin r → Bool, g a*f (Fin.append a (Fin.append p y))) = c*g p*h y)
    (p : Fin r → Bool) (y : Fin s → Bool) :
    (∑ a : Fin r → Bool, sourceKBasis.symm.action g (fun i => !(a i)) *
      sourceKBasis.symm.action f (Fin.append a (Fin.append p y))) =
      c*sourceKBasis.symm.action g p*sourceKBasis.symm.action h y := by
  change (∑ a : Fin r → Bool,
    Signature.coordinateAction (fun _ => KInverse) g (fun i => !(a i)) *
    Signature.coordinateAction (fun _ => KInverse) f (Fin.append a (Fin.append p y))) =
    c*Signature.coordinateAction (fun _ => KInverse) g p*Signature.coordinateAction (fun _ => KInverse) h y
  rw [contraction_action KInverse inverseK_orthogonal]
  have he : (fun w : Fin (r+s) → Bool => ∑ a : Fin r → Bool,
      g a*f (Fin.append a w)) =
    (fun w => c*g (fun i => w (Fin.castAdd s i))*h (fun i => w (Fin.natAdd r i))) := by
    funext w
    simpa only [Fin.append_castAdd_natAdd] using step
      (fun i => w (Fin.castAdd s i)) (fun i => w (Fin.natAdd r i))
  rw [he, action_product]

end
end Paper2.SourceFaithful.SourceStatements.Replication
