import Paper2.Paper1ProvedOddUnaryNRInheritance

/-! Literal coefficient tests for the small sheared rows. These tests are
derived from the same exact tensor criterion used by the high-arity descent. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K]

theorem generator_closed {n : ℕ} {f : Holant.Signature K n}
    (hf : Generator n f) : Closed f := by
  let E : (Σ _i : Fin 1,Fin n) ≃ Fin n :=
    ⟨fun p => p.2,fun j => ⟨0,j⟩,
      (by rintro ⟨i,j⟩;have hi := Fin.eq_zero i;subst i;rfl),(by intro j;rfl)⟩
  let D : TensorDecomposition K n :=
    {count:=1,arity:=fun _ => n,factor:=fun _ => f,ports:=E,scale:=1}
  refine Or.inr ⟨D,(fun _ => hf),?_⟩
  funext x
  simp [TensorDecomposition.value,D,E]

theorem unary_word (x : Fin 1 → Bool) : x=fun _ => x 0 := by
  funext i
  exact congrArg x (Fin.eq_zero i)

theorem closed_unary_iff (f : Holant.Signature K 1) :
    Closed f ↔ f (fun _ => true)=0 ∨ f (fun _ => false)=2*f (fun _ => true) := by
  constructor
  · intro hf
    by_cases zero : f (fun _ => true)=0
    · exact Or.inl zero
    · right
      have inherited := (closed_inheritance hf).1 (fun _ => true) 0 rfl zero
      have word : Function.update (fun _ : Fin 1 => true) 0 false=(fun _ => false) := by
        funext i
        have hi := Fin.eq_zero i
        simp [hi]
      simpa only [word] using inherited
  · rintro (zero|ratio)
    · apply generator_closed
      left
      refine ⟨rfl,f (fun _ => false),?_⟩
      funext x
      rw [unary_word x]
      cases x 0 <;> simp [pin,Holant.weight,zero]
    · apply generator_closed
      right
      refine ⟨by omega,f (fun _ => true),?_⟩
      funext x
      rw [unary_word x]
      cases x 0 <;> simp [row,Holant.weight,ratio]

theorem outside_unary (f : Holant.Signature K 1) (outside : ¬Closed f) :
    f (fun _ => true)≠0 ∧ f (fun _ => false)≠2*f (fun _ => true) := by
  rw [closed_unary_iff] at outside
  exact not_or.mp outside

end
end Paper2.Paper1Proved.OddUnary.NR

