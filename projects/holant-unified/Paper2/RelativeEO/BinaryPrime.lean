import Paper2.RelativeEO.ARSMatching

/-! Both nonzero off-diagonal entries force genuine tensor primality. The proof
uses the exact two-by-two determinant identity of every ordered unary product. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable

@[simp] theorem binWord_zero (a b : Bool) : binWord a b 0 = a := rfl
@[simp] theorem binWord_one (a b : Bool) : binWord a b 1 = b := rfl

theorem unaryTensor_apply (u v : Signature AlgebraicComplex 1) (x : Fin 2 → Bool) :
    Signature.tensor u v x = u (fun _ => x 0) * v (fun _ => x 1) := by
  change u (fun i => x (Fin.castAdd 1 i)) * v (fun i => x (Fin.natAdd 1 i)) = _
  congr 1 <;> congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem reindexed_unaryTensor_minor (e : Equiv.Perm (Fin 2))
    (u v : Signature AlgebraicComplex 1) :
    let g := Tensor.reindex e (Signature.tensor u v)
    g (binWord false false) * g (binWord true true) =
      g (binWord false true) * g (binWord true false) := by
  dsimp only
  simp only [Tensor.reindex_apply,unaryTensor_apply]
  have h00 : binWord false false = (fun _ => false) := by funext i; fin_cases i <;> rfl
  have h11 : binWord true true = (fun _ => true) := by funext i; fin_cases i <;> rfl
  rw [h00,h11]
  generalize h0 : e 0 = i
  generalize h1 : e 1 = j
  fin_cases i <;> fin_cases j
  · rfl
  · change (u (fun _ => false) * v (fun _ => false)) * (u (fun _ => true) * v (fun _ => true)) =
      (u (fun _ => false) * v (fun _ => true)) * (u (fun _ => true) * v (fun _ => false))
    ring
  · change (u (fun _ => false) * v (fun _ => false)) * (u (fun _ => true) * v (fun _ => true)) =
      (u (fun _ => true) * v (fun _ => false)) * (u (fun _ => false) * v (fun _ => true))
    ring
  · change (u (fun _ => false) * v (fun _ => false)) * (u (fun _ => true) * v (fun _ => true)) =
      (u (fun _ => true) * v (fun _ => true)) * (u (fun _ => false) * v (fun _ => false))
    ring

/-- Literal nonsingular EO binaries are prime, including arbitrary phases. -/
theorem eoSignature_tensorPrime (a b : AlgebraicComplex) (ha : a ≠ 0) (hb : b ≠ 0) :
    TensorPrime (eoSignature a b) := by
  refine ⟨eoSignature_ne_zero_left a b ha,?_⟩
  intro m k hm hk e u v he
  have hcard : m + k = 2 := by simpa using Fintype.card_congr e
  have hm1 : m = 1 := by omega
  have hk1 : k = 1 := by omega
  subst m
  subst k
  have hh := reindexed_unaryTensor_minor e u v
  dsimp only at hh
  rw [he] at hh
  change (0 : AlgebraicComplex) * 0 = a*b at hh
  have hz : (0 : AlgebraicComplex) = a*b := by simpa only [zero_mul] using hh
  exact mul_ne_zero ha hb hz.symm

end Paper2.RelativeEO
