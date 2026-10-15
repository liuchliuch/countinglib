import Paper2.DegreeCSP.OriginalContextCommonPhaseIndex
import Paper2.DegreeCSP.OriginalContextCommonPhasePadding

/-! One common original-language phase, obtained by finite enumeration of
actual supported row pairs and actual products of their unary contexts. -/
namespace Paper2.DegreeCSP.OriginalContextCommonPhase
open Tractable TensorDecomposition
open OriginalContextCommonPhaseIndex (RowPair rowPair count enumeration)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def contextForPair (F : SignatureFamily AlgebraicComplex) (k : ℕ) (p : RowPair F) :
    Presentation AlgebraicComplex (Fin 1) :=
  rowContext p.2.1.val p.2.2.val p.1.val.2 k

theorem contextForPair_uses (F : SignatureFamily AlgebraicComplex) (k : ℕ)
    (hp0 : (⟨1, literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hp1 : (⟨1, literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hX : (⟨2, kernelSignature (Signature.disequality (K := AlgebraicComplex))⟩ :
      AnySignature AlgebraicComplex) ∈ F) (p : RowPair F) :
    (contextForPair F k p).Uses F :=
  TwoWordContext.uses p.2.1.val p.2.2.val F p.1.val.2 p.1.property hp0 hp1 hX (copies k)

theorem contextForPair_hidden (F : SignatureFamily AlgebraicComplex) {k : ℕ}
    (hk : 0 < k) (p : RowPair F) :
    PartialUnaryProducts.HiddenDivisible (contextForPair F k p) k :=
  rowContext_hidden hk p.2.1.val p.2.2.val p.1.val.2

theorem contextForPair_value_false (F : SignatureFamily AlgebraicComplex) {k : ℕ}
    (hk : 0 < k) (p : RowPair F) :
    (contextForPair F k p).value ![false] = p.1.val.2 p.2.1.val :=
  rowContext_value_false hk p.2.1.val p.2.2.val p.1.val.2

theorem contextForPair_value_true (F : SignatureFamily AlgebraicComplex) {k : ℕ}
    (hk : 0 < k) (p : RowPair F) :
    (contextForPair F k p).value ![true] = p.1.val.2 p.2.2.val :=
  rowContext_value_true hk p.2.1.val p.2.2.val p.1.val.2

/-- One phase governs every pair of nonzero original coefficients. Its
exponent is the true forward plus reversed boundary incidence receipt. -/
theorem common_phase (F : SignatureFamily AlgebraicComplex) (hF : F.Finite)
    {k : ℕ} (hk : 0 < k)
    (hp0 : (⟨1, literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hp1 : (⟨1, literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hX : (⟨2, kernelSignature (Signature.disequality (K := AlgebraicComplex))⟩ :
      AnySignature AlgebraicComplex) ∈ F)
    (affine : ∀ g : Signature AlgebraicComplex 1, Generated F k g → Affine g) :
    ∃ θ : AlgebraicComplex, θ ^ k = 1 ∧
      ∀ {n : ℕ} (f : Signature AlgebraicComplex n),
        (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ F →
        ∀ (x y : Fin n → Bool), f x ≠ 0 → f y ≠ 0 →
          (f y / f x) ^ 4 = θ ^ TwoWordContext.boundaryCount x y (k - 1) := by
  let e := enumeration F hF
  let P : Fin (count F hF) → Presentation AlgebraicComplex (Fin 1) :=
    fun i => contextForPair F k (e.symm i)
  have uses : ∀ i, (P i).Uses F :=
    fun i => contextForPair_uses F k hp0 hp1 hX (e.symm i)
  have hidden : ∀ i, PartialUnaryProducts.HiddenDivisible (P i) k :=
    fun i => contextForPair_hidden F hk (e.symm i)
  have h0 : ∀ i, (P i).value ![false] ≠ 0 := by
    intro i
    rw [contextForPair_value_false F hk]
    exact (e.symm i).2.1.property
  have h1 : ∀ i, (P i).value ![true] ≠ 0 := by
    intro i
    rw [contextForPair_value_true F hk]
    exact (e.symm i).2.2.property
  obtain ⟨θ, hθ, hphase⟩ := PartialUnaryProducts.common_phase hk affine P uses hidden h0 h1
  refine ⟨θ, hθ, ?_⟩
  intro n f hf x y hx hy
  let p := rowPair F hf x y hx hy
  have hi := hphase (e p)
  change ((contextForPair F k (e.symm (e p))).value ![true] /
    (contextForPair F k (e.symm (e p))).value ![false]) ^ 4 =
      θ ^ (contextForPair F k (e.symm (e p))).degree (Sum.inl 0) at hi
  rw [e.symm_apply_apply] at hi
  change ((rowContext x y f k).value ![true] / (rowContext x y f k).value ![false]) ^ 4 =
    θ ^ (rowContext x y f k).degree (Sum.inl 0) at hi
  rw [rowContext_value_true hk, rowContext_value_false hk, rowContext_degree] at hi
  exact requested_exponent x y hθ hi

end
end Paper2.DegreeCSP.OriginalContextCommonPhase
