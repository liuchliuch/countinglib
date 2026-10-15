import Paper2.HeightOne.Dihedral.HighArityCommonFactor
import Paper2.HeightOne.TensorPrimeTools
import Holant.Dihedral.CompatibleCoefficientLine.PortAlignment

/-! Exact reconstruction from four sampled matching products with a common
projective binary line. Vanishing cards have zero complementary factors, so
neither individual samples nor entire xor sectors are assumed nonzero. -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Holant.Marked
open Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem sum_factor_not_tensorPrime {k l n : ℕ} (hk : 0 < k) (hl : 0 < l)
    (p : Fin k ⊕ Fin l ≃ Fin n) (a : Paper2.Signature Scalar k)
    (b : Paper2.Signature Scalar l) (q : Paper2.Signature Scalar n)
    (he : q = Holant.Tensor.reindex p (Holant.Tensor.tensor a b)) : ¬ Paper2.TensorPrime q := by
  intro hp
  apply hp.2 k l hk hl (finSumFinEquiv.symm.trans p) a b
  funext x
  rw [he]
  simp only [Paper2.Tensor.reindex,Paper2.Signature.tensor_apply,Holant.Tensor.reindex,Holant.Tensor.tensor,
    Equiv.trans_apply,finSumFinEquiv_symm_apply_castAdd,finSumFinEquiv_symm_apply_natAdd]

private theorem close_liftPair {n : ℕ} (o : Equiv.Perm (Fin (n+2)))
    (q : Holant.Signature Scalar (n+4)) (γ : Bool) (t : Scalar) :
    close γ t (Holant.Tensor.reindex (liftPair o).symm q) =
      Holant.Tensor.reindex o.symm (close γ t q) := by
  funext x
  simp only [close,Holant.Tensor.reindex]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  exact congrArg q (word_liftPair o a b x)

private theorem matching_extract_first {n r : ℕ}
    (p : (Fin r × Bool) ≃ Fin (n+2)) (A : Fin r → Mat) (κ : Scalar)
    (e : Fin r) (hp0 : p (e,false) = 0) (hp1 : p (e,true) = 1)
    (a b : Bool) (x : Fin n → Bool) :
    productValue p A κ (pair a b x) = A e a b *
      (κ * ∏ d ∈ {e}ᶜ,A d (pair false false x (p (d,false)))
        (pair false false x (p (d,true)))) := by
  have hi : insertPair (p (e,false)) (p (e,true)) a b (pair false false x) = pair a b x := by
    rw [hp0,hp1]
    funext j
    refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun l => ?_) k) j
    · simp [insertPair,pair]
    · simp [insertPair,pair]
    · simp [insertPair,pair,Fin.succ_succ_ne_one]
  simpa only [hi] using product_extract_edge p A κ e a b (pair false false x)

/-- A fixed matching and at most one pairwise factor-line discrepancy force
a proper binary factor of the entire ancestor, with its original ports and
all four coefficients reconstructed by exact two-phase inversion. -/
theorem four_cards_not_tensorPrime {n r : ℕ} (hr : 2 ≤ r)
    (q : Paper2.Signature Scalar (n+4)) (t₀ t₁ : Scalar) (ht : t₀ ≠ t₁)
    (p : (Fin r × Bool) ≃ Fin (n+2))
    (A : {i : Sample // close i.1 (phase t₀ t₁ i) q ≠ 0} → Fin r → Mat)
    (κ : {i : Sample // close i.1 (phase t₀ t₁ i) q ≠ 0} → Scalar)
    (he : ∀ i,close i.val.1 (phase t₀ t₁ i.val) q = productValue p (A i) (κ i))
    (hp : ∀ i j (e f : Fin r),e ≠ f →
      ProjectivelyEqual (A i e) (A j e) ∨ ProjectivelyEqual (A i f) (A j f)) :
    ¬ Paper2.TensorPrime q := by
  classical
  intro hprime
  have hn : ∃ i : Sample,close i.1 (phase t₀ t₁ i) q ≠ 0 := by
    by_contra hz
    push Not at hz
    have hf := four_card_inversion t₀ t₁ ht q (0 : Mat) (fun _ => 0) (by
      intro i a b x
      rw [hz i]
      simp)
    apply hprime.1
    funext x
    have hh := hf (x 0) (x 1) (tail x 0) (tail x 1) (tail (tail x))
    rw [pair_eta,pair_eta] at hh
    simpa using hh
  obtain ⟨i₀,hi₀⟩ := hn
  let j₀ : {i : Sample // close i.1 (phase t₀ t₁ i) q ≠ 0} := ⟨i₀,hi₀⟩
  obtain ⟨e,hedge⟩ := common_projective_factor hr A j₀ hp
  let B := A j₀ e
  have huv : p (e,false) ≠ p (e,true) := by
    intro h
    have hb := congrArg Prod.snd (p.injective h)
    cases hb
  let o := pairOrder (p (e,false)) (p (e,true))
  let p' := p.trans o.symm
  have hp0 : p' (e,false) = 0 := by
    change o.symm (p (e,false)) = 0
    rw [← pairOrder_first _ _ huv]
    exact Equiv.symm_apply_apply o 0
  have hp1 : p' (e,true) = 1 := by
    change o.symm (p (e,true)) = 1
    rw [← pairOrder_second (p (e,false)) (p (e,true))]
    exact Equiv.symm_apply_apply o 1
  let q' := Holant.Tensor.reindex (liftPair o).symm q
  have hsample (i : Sample) : ∃ H : Holant.Signature Scalar n,
      ∀ a b x,close i.1 (phase t₀ t₁ i) q' (pair a b x) = B a b * H x := by
    by_cases hzero : close i.1 (phase t₀ t₁ i) q = 0
    · refine ⟨0,?_⟩
      intro a b x
      rw [close_liftPair,hzero]
      simp [Holant.Tensor.reindex]
    · let j : {i : Sample // close i.1 (phase t₀ t₁ i) q ≠ 0} := ⟨i,hzero⟩
      obtain ⟨c,hc,hcB⟩ := hedge j
      refine ⟨fun x => c * (κ j * ∏ d ∈ {e}ᶜ,
        A j d (pair false false x (p' (d,false))) (pair false false x (p' (d,true)))),?_⟩
      intro a b x
      rw [close_liftPair,he j]
      change productValue p' (A j) (κ j) (pair a b x) = _
      rw [matching_extract_first p' (A j) (κ j) e hp0 hp1,hcB]
      simp only [Holant.Marked.scale]
      dsimp only [B]
      ring
  choose H hH using hsample
  let R := inverseSlices t₀ t₁ H
  have hq' : q' = Holant.Tensor.reindex (factorPorts n)
      (Holant.Tensor.tensor (Holant.Tractable.kernelSignature B) R) :=
    tensor_factor_of_slices q' B R (four_card_inversion t₀ t₁ ht q' B H hH)
  have hq : q = Holant.Tensor.reindex ((factorPorts n).trans (liftPair o))
      (Holant.Tensor.tensor (Holant.Tractable.kernelSignature B) R) := by
    have hh := congrArg (Holant.Tensor.reindex (liftPair o)) hq'
    simpa only [q',Holant.Tensor.reindex_trans,Equiv.symm_trans_self,
      Holant.Tensor.reindex_refl] using hh
  exact sum_factor_not_tensorPrime (by decide : 0 < 2) (by omega : 0 < n+2)
    _ _ _ q hq hprime

end
end Paper2.HeightOne.Dihedral.HighArity

