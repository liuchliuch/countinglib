import Paper2.DegreeCSP.GeneratedOrthogonality

/-! Boundary relabeling changes no constraint, occurrence, hidden variable,
or degree. This supplies genuine transposed partial tables. -/
namespace Paper2.DegreeCSP
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Presentation

abbrev renameBoundary {K B C : Type} (P : Presentation K B) (e : B ≃ C) :
    Presentation K C where
  hiddenCount := P.hiddenCount
  constraints := P.constraints
  arity := P.arity
  constraint := P.constraint
  scope c i := Equiv.sumCongr e (Equiv.refl _) (P.scope c i)

def renameFiber {K B C : Type} (P : Presentation K B) (e : B ≃ C)
    (v : B ⊕ Fin P.hiddenCount) :
    (P.renameBoundary e).Fiber (Equiv.sumCongr e (Equiv.refl _) v) ≃ P.Fiber v where
  toFun p := ⟨p.val,(Equiv.sumCongr e (Equiv.refl _)).injective p.property⟩
  invFun p := ⟨p.val,congrArg (Equiv.sumCongr e (Equiv.refl _)) p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rename_degree {K B C : Type} (P : Presentation K B) (e : B ≃ C)
    (v : B ⊕ Fin P.hiddenCount) :
    (P.renameBoundary e).degree (Equiv.sumCongr e (Equiv.refl _) v) = P.degree v :=
  Nat.card_congr (P.renameFiber e v)

theorem rename_divisible {K B C : Type} (P : Presentation K B) (e : B ≃ C)
    {k : ℕ} (h : P.DegreeDivisible k) : (P.renameBoundary e).DegreeDivisible k := by
  intro v
  obtain ⟨w,rfl⟩ := (Equiv.sumCongr e (Equiv.refl _)).surjective v
  rw [P.rename_degree e w]
  exact h w

theorem rename_uses {K B C : Type} (P : Presentation K B) (e : B ≃ C)
    {F : SignatureFamily K} (h : P.Uses F) : (P.renameBoundary e).Uses F := h

theorem rename_value {K B C : Type} [CommSemiring K]
    (P : Presentation K B) (e : B ≃ C) (x : C → Bool) :
    (P.renameBoundary e).value x = P.value (fun i => x (e i)) := by
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.prod_congr rfl
  intro c _
  congr 1
  funext i
  change Sum.elim x y (Equiv.sumCongr e (Equiv.refl _) (P.scope c i)) = _
  cases h : P.scope c i <;> simp [h]

end Presentation

theorem generated_reindex {K : Type} [CommSemiring K]
    {F : SignatureFamily K} {k n m : ℕ} {f : Signature K n}
    (h : Generated F k f) (e : Fin n ≃ Fin m) :
    Generated F k (fun x => f (fun i => x (e i))) := by
  obtain ⟨P,hF,hk,hf⟩ := h
  refine ⟨P.renameBoundary e,P.rename_uses e hF,P.rename_divisible e hk,?_⟩
  funext x
  rw [Presentation.rename_value,hf]

namespace OriginalBO
/-- Transposing a generated binary table uses a literal boundary permutation. -/
theorem generated_binary_transpose_bo {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hBO : AllGeneratedOriginalBO F k) (f : Signature AlgebraicComplex 2)
    (hf : Generated F k f) :
    BlockOrthogonal (fun b c : Bool => (f ![c,b] : ℂ)) := by
  let e : Fin 2 ≃ Fin 2 := Equiv.swap 0 1
  have h := generated_binary_bo hBO (fun x => f (fun i => x (e i)))
    (generated_reindex hf e)
  convert h using 1
  funext b c
  congr 2
  funext i
  fin_cases i <;> simp [e,Equiv.swap_apply_def]

end OriginalBO
end
end Paper2.DegreeCSP
