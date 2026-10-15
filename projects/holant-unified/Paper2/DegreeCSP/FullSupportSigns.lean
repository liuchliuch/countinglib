import Paper2.DegreeCSP.HigherArityPinPadding
import Paper2.DegreeCSP.GeneratedCoordinateRows
import Paper2.DegreeCSP.PinGaugeCoefficients

/-! A full-support coefficient normal form from BO of the genuine
all-degree-generated family. Literal pins supply the ordered gauge witness,
and actual generated squares supply every coordinate cross equation. -/
namespace Paper2.DegreeCSP
open scoped BigOperators
open Tractable TensorDecomposition AxisRatioSigns
noncomputable section

/-- A generated full-support table already has exact coordinate equations;
no extra pin-padding is needed for this intermediate table. -/
theorem generated_full_support_signs {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    (hBO : OriginalBO.AllGeneratedOriginalBO F k)
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (hne : ∀ x,f x ≠ 0) :
    (∀ i,axisRatio f i ≠ 0) ∧
      ∃ P : (Fin n → Bool) → Bool,P zeroWord = false ∧ ∀ x,
        f x = f zeroWord * (∏ i,if x i then axisRatio f i else 1) *
          (if P x then -1 else 1) := by
  apply PinGaugeCoefficients.signs f hne 0
  intro i x hx
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have h := OriginalBO.squared_cross_rows_algebraic hBO f hf hne i x zeroWord
    have hxf : Function.update x i false = x := by
      funext j
      by_cases hji : j = i
      · subst j; simp [Function.update,hx]
      · exact Function.update_of_ne hji false x
    have hzf : Function.update zeroWord i false = (zeroWord : Fin (n+1) → Bool) := by
      funext j
      by_cases hji : j = i
      · subst j; simp [Function.update,zeroWord]
      · exact Function.update_of_ne hji false zeroWord
    simpa [PinGaugeCoefficients.padded,PinGaugeCoefficients.weight,hxf,hzf] using h

/-- The sign is explicitly reconstructed. Quadraticity and a phase common to
the whole finite language require further generated contraction constraints. -/
theorem full_support_signs (F : SignatureFamily AlgebraicComplex)
    {t : ℕ} (ht : 0 < t) (hBO : OriginalBO.AllGeneratedOriginalBO F (t+1))
    {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hp : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hne : ∀ x,f x ≠ 0) :
    (∀ i,axisRatio f i ≠ 0) ∧
      ∃ P : (Fin n → Bool) → Bool,P zeroWord = false ∧ ∀ x,
        f x = f zeroWord * (∏ i,if x i then axisRatio f i else 1) *
          (if P x then -1 else 1) := by
  let H : Signature AlgebraicComplex n := PinGaugeCoefficients.padded f t
  have hH : Generated F (t+1) H := by
    change Generated F (t+1) (fun x => f x * ∏ i,
      f (Function.update (fun _ => false) i (x i)) ^ t)
    exact HigherArityPinPadding.generated F f hf hp ht
  have hHne (x : Fin n → Bool) : H x ≠ 0 :=
    PinGaugeCoefficients.padded_nonzero f hne t x
  apply PinGaugeCoefficients.signs f hne t
  intro i x hx
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    have h := OriginalBO.squared_cross_rows_algebraic hBO H hH hHne i x zeroWord
    have hxf : Function.update x i false = x := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [Function.update,hx]
      · exact Function.update_of_ne hji false x
    have hzf : Function.update zeroWord i false = (zeroWord : Fin (n+1) → Bool) := by
      funext j
      by_cases hji : j = i
      · subst j
        simp [Function.update,zeroWord]
      · exact Function.update_of_ne hji false zeroWord
    simpa only [hxf,hzf] using h

end
end Paper2.DegreeCSP
