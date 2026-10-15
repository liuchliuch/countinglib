import Paper2.SourceFaithful.SourceStatements.PhaseProductParityDeck
import Paper2.HeightOne.PhaseCards.PhaseProduct

/-! Arity-two P_N tensors are exactly zero or a scaled negative-root
complementary pair, independent of its offset and port enumeration. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards
open scoped BigOperators

lemma BinaryPhase.reindex {N : ℕ} {ι κ : Type} [Fintype ι] [Fintype κ]
    {f : Tensor AlgebraicComplex ι} (hf : BinaryPhase N f) (e : ι ≃ κ) :
    BinaryPhase N (Tensor.reindex e f) := by
  exact ⟨hasParity_reindex e f hf.1,fun x => hf.2 (fun i => x (e i))⟩

lemma BinaryPhase.scale {N : ℕ} {ι : Type} [Fintype ι]
    {f : Tensor AlgebraicComplex ι} (hf : BinaryPhase N f) (c : AlgebraicComplex) :
    BinaryPhase N (c • f) := by
  by_cases hc : c = 0
  · subst c
    simpa using (show BinaryPhase N (0 : Tensor AlgebraicComplex ι) from
      ⟨hasParity_zero,fun _ => Or.inl ⟨rfl,rfl⟩⟩)
  · exact ⟨(hasParity_scale_iff c hc f).mpr hf.1,
      fun x => (RootComplement.smul_iff _ _ c hc).mpr (hf.2 x)⟩

lemma binaryPhase_twoPoint {N : ℕ} (hN : 0 < N) (a : Fin 2 → Bool)
    (r : AlgebraicComplex) (hr : PhaseRatio N 1 r) :
    BinaryPhase N (twoPoint a r) := by
  obtain ⟨s,he⟩ := hr
  have hs : Root N (s.val : AlgebraicComplex) := root_of_unity s
  have hs0 := root_ne_zero hN hs
  have he' : r = -(s.val : AlgebraicComplex) := by simpa using he
  rw [he']
  have ha : a ≠ fun i => !(a i) := by
    intro heq
    have h := congrFun heq 0
    cases a 0 <;> simp at h
  constructor
  · intro x y hx hy
    have live : ∀ x, twoPoint a (-(s.val : AlgebraicComplex)) x ≠ 0 →
        x = a ∨ x = fun i => !(a i) := by
      intro x hx
      by_contra h
      push Not at h
      exact hx (by simp [twoPoint,point,h])
    have hp : parity (fun i => !(a i)) = parity a := by
      have h : ∀ a : Fin 2 → Bool, parity (fun i => !(a i)) = parity a := by decide
      exact h a
    rcases live x hx with rfl | rfl <;> rcases live y hy with rfl | rfl <;> simp [hp]
  · intro x
    by_cases hx : x = a
    · subst x
      simpa [twoPoint,point,ha,ha.symm] using
        (show RootComplement N 1 (-(s.val : AlgebraicComplex)) from
          Or.inr ⟨s.val,hs,one_ne_zero,by ring⟩)
    by_cases hxc : x = fun i => !(a i)
    · subst x
      refine Or.inr ⟨(s.val : AlgebraicComplex)⁻¹,?_,?_,?_⟩
      · change ((s.val : AlgebraicComplex)⁻¹) ^ N = 1
        rw [inv_pow,hs,inv_one]
      · simp [twoPoint,point,ha.symm,hs0]
      · simp [twoPoint,point,ha,ha.symm,hs0]
    · have hca : (fun i => !(x i)) ≠ a := by
        intro heq
        apply hxc
        simpa only [Bool.not_not] using
          congrArg (fun w : Fin 2 → Bool => fun i => !(w i)) heq
      have hcc : (fun i => !(x i)) ≠ fun i => !(a i) := by
        intro heq
        exact hx (funext (fun i => Bool.not_injective (congrFun heq i)))
      exact Or.inl ⟨by simp [twoPoint,point,hx,hxc],by simp [twoPoint,point,hca,hcc]⟩

theorem binary_phaseProduct {N : ℕ} (hN : 0 < N) {ι : Type} [Fintype ι]
    (hcard : Fintype.card ι = 2) (f : Tensor AlgebraicComplex ι)
    (hf : PhaseProduct N f) : BinaryPhase N f := by
  rcases hf with rfl | ⟨n,D,e,hD,rfl⟩
  · exact ⟨hasParity_zero,fun _ => Or.inl ⟨rfl,rfl⟩⟩
  have hn : n = 2 := by simpa using (Fintype.card_congr e).trans hcard
  subst n
  rcases D with ⟨count,arity,factor,ports,scale⟩
  have har : ∀ i, 2 ≤ arity i := by
    intro i
    obtain ⟨k,a,r,he,_,_⟩ := hD i
    change arity i = 2 * (k + 1) at he
    omega
  have hs : ∑ i, arity i = 2 := by
    simpa using Fintype.card_congr ports
  have hle : count * 2 ≤ 2 := by
    calc
      count * 2 = ∑ _i : Fin count, 2 := by simp
      _ ≤ ∑ i, arity i := Finset.sum_le_sum (fun i _ => har i)
      _ = 2 := hs
  have hc : count = 1 := by
    have hn0 : count ≠ 0 := by intro he; subst count; simp at hs
    omega
  subst count
  have ha : arity = fun _ => 2 := by
    funext i
    have hi := Fin.eq_zero i
    subst i
    simpa using hs
  subst arity
  change ∀ i, EvenPhaseBlock N (factor i) at hD
  obtain ⟨k,a,r,hk,hr,he⟩ := hD 0
  change 2 = 2 * (k + 1) at hk
  have hk0 : k = 0 := by omega
  subst k
  have hb : BinaryPhase N (factor 0) := by
    rw [he]
    exact binaryPhase_twoPoint hN a r hr
  let ep : Fin 2 ≃ Fin 2 := (Equiv.uniqueSigma (fun _ : Fin 1 => Fin 2)).symm.trans ports
  have hv : (TensorDecomposition.mk 1 (fun _ => 2) factor ports scale).value =
      (scale : AlgebraicComplex) • Tensor.reindex ep (factor 0) := by
    funext x
    simp [TensorDecomposition.value,Tensor.reindex,ep]
  rw [hv]
  exact ((hb.reindex ep).scale scale).reindex e

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity
