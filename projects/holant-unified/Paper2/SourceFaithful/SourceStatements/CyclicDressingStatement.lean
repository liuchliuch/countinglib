import Paper2.HeightOne.Cyclic.DressingPhases
import Paper2.HeightOne.Cyclic.ActualDressing

/-! The full four-port dressing statement, including the image obstruction at
even orders and the literal representative scales in the actual native graph. -/
namespace Paper2.SourceFaithful.SourceStatements.CyclicDressing
noncomputable section
open Paper2 Tractable HeightOne.PhaseCards HeightOne.Cyclic
open HeightOne.GroupSplit HeightOne.GroupSplit.MatrixGroup
open Paper2.HighHeightNormalization
open scoped BigOperators

lemma dressing_square {N : ℕ} (r : Fin 4 → rootsOfUnity N AlgebraicComplex) :
    r 0 ^ 2 = ((dressingMap r).2 0 * (dressingMap r).2 1 *
      (dressingMap r).2 2) / (dressingMap r).1 := by
  apply Subtype.ext
  apply Units.ext
  dsimp [dressingMap]
  push_cast
  simp only [Fin.prod_univ_four]
  change ((r 0).val : AlgebraicComplex) ^ 2 =
    (((r 0).val : AlgebraicComplex) * (r 1).val *
      (((r 0).val : AlgebraicComplex) * (r 2).val) *
      (((r 0).val : AlgebraicComplex) * (r 3).val)) /
      (((r 0).val : AlgebraicComplex) * (r 1).val * (r 2).val * (r 3).val)
  field_simp

/-- The source image criterion holds at every order, including even orders. -/
theorem dressing_image_iff {N : ℕ}
    (q : rootsOfUnity N AlgebraicComplex × (Fin 3 → rootsOfUnity N AlgebraicComplex)) :
    (∃ r, dressingMap r = q) ↔
      ∃ a : rootsOfUnity N AlgebraicComplex,
        a ^ 2 = (q.2 0 * q.2 1 * q.2 2) / q.1 := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r 0, dressing_square r⟩
  · rintro ⟨a, ha⟩
    refine ⟨![a, q.2 0 / a, q.2 1 / a, q.2 2 / a], ?_⟩
    apply Prod.ext
    · change (∏ i : Fin 4, (![a, q.2 0 / a, q.2 1 / a, q.2 2 / a] : Fin 4 → _) i) = q.1
      simp only [Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Matrix.cons_val_three]
      change a * (q.2 0 / a) * (q.2 1 / a) * (q.2 2 / a) = q.1
      apply Subtype.ext
      apply Units.ext
      have ha' := congrArg (fun z : rootsOfUnity N AlgebraicComplex =>
        (z.val : AlgebraicComplex)) ha
      push_cast at ha' ⊢
      change (a.val : AlgebraicComplex) ^ 2 =
        (q.2 0).val * (q.2 1).val * (q.2 2).val / q.1.val at ha'
      change (a.val : AlgebraicComplex) * ((q.2 0).val / a.val) *
        ((q.2 1).val / a.val) * ((q.2 2).val / a.val) = q.1.val
      calc
        _ = ((q.2 0).val * (q.2 1).val * (q.2 2).val) /
            (a.val : AlgebraicComplex) ^ 2 := by field_simp
        _ = q.1.val := by rw [ha']; field_simp
    · funext i
      fin_cases i <;> simp [dressingMap]

lemma transfer_of_walshBinary {B : AMat} {k s : AlgebraicComplex}
    (hB : walshBinary B = k • plusKernel s) :
    transfer B = (2 * k) • phase s := by
  have hi : walshInv.transpose = walshInv := by
    funext i j
    cases i <;> cases j <;> rfl
  have hrec : B = walsh * walshBinary B * walsh := by
    rw [walshBinary, hi]
    simp only [← Matrix.mul_assoc, walsh_mul_walshInv, Matrix.one_mul]
    rw [Matrix.mul_assoc, walshInv_mul_walsh, Matrix.mul_one]
  rw [hrec, hB]
  funext i j
  cases i <;> cases j <;>
    simp [transfer, walsh, plusKernel, phase, balanced, X,
      Signature.disequality, Matrix.mul_apply, Matrix.smul_apply] <;>
    field_simp <;> ring

/-- Four specified actual representatives, with exactly the source Walsh
matrices. No completeness or safety hypothesis on the binary group is needed. -/
theorem actual_dressing {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (B : rootsOfUnity N AlgebraicComplex → AMat)
    (k : rootsOfUnity N AlgebraicComplex → AlgebraicComplex)
    (hactual : ∀ s, NetworkRealizable F (kernelSignature (B s)))
    (hk : ∀ s, k s ≠ 0)
    (hwalsh : ∀ s, walshBinary (B s) = k s • plusKernel s.val)
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable F f)
    (r : Fin 4 → rootsOfUnity N AlgebraicComplex) :
    ∃ h : Signature AlgebraicComplex 4,
      NetworkRealizable F h ∧
      (2 ^ 4 * ∏ j, k (r j) : AlgebraicComplex) ≠ 0 ∧
      walshCoordinates h = fun x =>
        (2 ^ 4 * ∏ j, k (r j)) *
        (∏ j, if x j then ((r j).val : AlgebraicComplex) else 1) *
        walshCoordinates f x := by
  refine ⟨attachmentSequence (fun j : Fin 4 => j) (fun j => B (r j)) f,
    attachmentSequence_realizable _ _ f hf (fun j => hactual (r j)), ?_, ?_⟩
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (Finset.prod_ne_zero_iff.mpr (fun j _ => hk (r j)))
  · rw [cyclic_attachmentSequence_walsh _ _ (fun j => 2 * k (r j))
      (fun j => ((r j).val : AlgebraicComplex))
      (fun j => transfer_of_walshBinary (hwalsh (r j))) f]
    rw [Finset.prod_mul_distrib]
    simp

/-- Literal source Lemma 5.23, retaining all three independent conclusions. -/
theorem source_5_23_image {N : ℕ}
    (q : rootsOfUnity N AlgebraicComplex × (Fin 3 → rootsOfUnity N AlgebraicComplex)) :
    (∃ r, dressingMap r = q) ↔
      (q.2 0 * q.2 1 * q.2 2) / q.1 ∈
        Set.range (fun a : rootsOfUnity N AlgebraicComplex => a ^ 2) := by
  rw [dressing_image_iff]
  rfl

theorem source_5_23_odd {N : ℕ} (hN : Odd N) :
    Function.Bijective (@dressingMap N) := odd_dressing_bijective hN

/-- All clauses of the source lemma, for a literal supplied quaternary and
specified actual representatives in their given orientation. -/
theorem source_5_23 {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (B : rootsOfUnity N AlgebraicComplex → AMat)
    (k : rootsOfUnity N AlgebraicComplex → AlgebraicComplex)
    (hactual : ∀ s, NetworkRealizable F (kernelSignature (B s)))
    (hk : ∀ s, k s ≠ 0)
    (hwalsh : ∀ s, walshBinary (B s) = k s • plusKernel s.val)
    (f : Signature AlgebraicComplex 4)
    (hf : (⟨4, f⟩ : AnySignature AlgebraicComplex) ∈ F) :
    (∀ r : Fin 4 → rootsOfUnity N AlgebraicComplex,
      ∃ h : Signature AlgebraicComplex 4, NetworkRealizable F h ∧
        (2 ^ 4 * ∏ j, k (r j) : AlgebraicComplex) ≠ 0 ∧
        ∀ x, walshCoordinates h x / (2 ^ 4 * ∏ j, k (r j)) =
          walshCoordinates f x *
            (∏ j, if x j then ((r j).val : AlgebraicComplex) else 1)) ∧
    (∀ q : rootsOfUnity N AlgebraicComplex × (Fin 3 → rootsOfUnity N AlgebraicComplex),
      (∃ r, dressingMap r = q) ↔
        (q.2 0 * q.2 1 * q.2 2) / q.1 ∈
          Set.range (fun a : rootsOfUnity N AlgebraicComplex => a ^ 2)) ∧
    (Odd N → Function.Bijective (@dressingMap N)) := by
  refine ⟨?_, source_5_23_image, source_5_23_odd⟩
  intro r
  obtain ⟨h, hh, hc, he⟩ := actual_dressing B k hactual hk hwalsh f
    (supplied_realizable hf) r
  refine ⟨h, hh, hc, ?_⟩
  intro x
  rw [he]
  dsimp only
  apply (div_eq_iff hc).2
  ring


end
end Paper2.SourceFaithful.SourceStatements.CyclicDressing

