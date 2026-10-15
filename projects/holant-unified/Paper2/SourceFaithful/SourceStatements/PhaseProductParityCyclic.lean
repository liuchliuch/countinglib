import Paper2.SourceFaithful.SourceStatements.PhaseProductParityDeck

/-! Source Lemma 5.12 with the literal zero-or-cyclic condition on every
ordered equal-bit contraction, including both orders of each residual pair. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.Cyclic
open HeightOne.PhaseCards EndpointSelfLoop

def CyclicContractions (N : ℕ) (f : Signature AlgebraicComplex 4) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (s : AlgebraicComplex), Root N s →
    SupportedOnParity (plusContraction i j hij s f) 0 ∧
      ∀ x, RootComplement N (plusContraction i j hij s f x)
        (plusContraction i j hij s f (fun k => !(x k)))

lemma RootComplement.reverse {N : ℕ} (hN : 0 < N) {a b : AlgebraicComplex}
    (h : RootComplement N a b) : RootComplement N b a := by
  rcases h with ⟨rfl,rfl⟩ | ⟨r,hr,ha,hb⟩
  · exact Or.inl ⟨rfl,rfl⟩
  · have hr0 := root_ne_zero hN hr
    refine Or.inr ⟨r⁻¹,?_,by rw [hb]; exact mul_ne_zero (neg_ne_zero.mpr hr0) ha,?_⟩
    · change (r⁻¹) ^ N = 1
      rw [inv_pow,hr,inv_one]
    · rw [hb]; field_simp

lemma parity_complement_two {ι : Type} [Fintype ι] (hc : Fintype.card ι = 2)
    (x : ι → Bool) : parity (fun i => !(x i)) = parity x := by
  let e : Fin 2 ≃ ι := (finCongr hc.symm).trans (Fintype.equivFin ι).symm
  have h : ∀ z : Fin 2 → Bool, parity (fun i => !(z i)) = parity z := by decide
  have he : weight (fun i : Fin 2 => !(x (e i))) = weight (fun i => !(x i)) :=
    weight_reindex e (fun i => !(x i))
  simpa only [parity,he,weight_reindex] using h (fun i => x (e i))

lemma even_two_constant {ι : Type} [Fintype ι] (hc : Fintype.card ι = 2)
    (x : ι → Bool) (hp : parity x = 0) :
    x = (fun _ => false) ∨ x = (fun _ => true) := by
  let e : Fin 2 ≃ ι := (finCongr hc.symm).trans (Fintype.equivFin ι).symm
  have hp' : parity (fun i => x (e i)) = 0 := by simpa only [parity,weight_reindex] using hp
  have h : ∀ z : Fin 2 → Bool, parity z = 0 →
      z = (fun _ => false) ∨ z = (fun _ => true) := by decide
  rcases h _ hp' with he | he
  · left; funext i; simpa using congrFun he (e.symm i)
  · right; funext i; simpa using congrFun he (e.symm i)

lemma cyclic_rows_all_pairs {N : ℕ} {f : Signature AlgebraicComplex 4}
    (h : QuaternaryRows N (f (fun _ => false)) (f (fun _ => true))
      (fun i => f (centralWord i (fun _ => false)))
      (fun i => f (flipAll (centralWord i (fun _ => false))))) :
    ∀ i j : Fin 4, i ≠ j →
      Relation N (f (fun _ => false)) (f (flipPair i j (fun _ => false)))
        (f (flipAll (flipPair i j (fun _ => false)))) (f (fun _ => true)) := by
  intro i j hij
  have geometry : ∀ i j : Fin 4, i ≠ j → ∃ k : Fin 3,
      flipPair i j (fun _ => false) = centralWord k (fun _ => false) ∨
        flipPair i j (fun _ => false) = flipAll (centralWord k (fun _ => false)) := by decide
  obtain ⟨k,hk | hk⟩ := geometry i j hij
  · rw [hk]; exact (h k).1
  · rw [hk,flipAll_flipAll]; exact (h k).2

theorem cyclic_local_iff {N : ℕ} (hN : 3 ≤ N) (f : Signature AlgebraicComplex 4)
    (heven : SupportedOnParity f 0) :
    CyclicContractions N f ↔
      CyclicPencils N (f (fun _ => false)) (f (fun _ => true))
        (fun i => f (centralWord i (fun _ => false)))
        (fun i => f (flipAll (centralWord i (fun _ => false)))) := by
  constructor
  · intro h
    have row (i j : Fin 4) (hij : i ≠ j) :
        Relation N (f (fun _ => false)) (f (flipPair i j (fun _ => false)))
          (f (flipAll (flipPair i j (fun _ => false)))) (f (fun _ => true)) := by
      apply (provedPhasePencil.phasePencil_7_1 N hN _ _ _ _).mpr
      intro s hs
      have hc := (h i j hij s hs).2 (restrict i j (fun _ => false))
      rw [← card_plus,← xorKernel_false_false,card_xor_apply,card_xor_apply,
        extendBits_restrict,extendBits_flipPair,extendBits_flipRemaining,extendBits_flipAll] at hc
      exact hc.safe
    intro i
    constructor
    · exact (provedPhasePencil.phasePencil_7_1 N hN _ _ _ _).mp
        (row 0 i.succ (by intro he; have := congrArg Fin.val he; simp at this))
    · exact (provedPhasePencil.phasePencil_7_1 N hN _ _ _ _).mp
        (by simpa only [flip_other_pair,flipAll_flipAll] using
          row (otherFirst i) (otherSecond i) (other_distinct i))
  · intro h i j hij s hs
    have hr := cyclic_rows_all_pairs (fun k =>
      ⟨(provedPhasePencil.phasePencil_7_1 N hN _ _ _ _).mpr (h k).1,
        (provedPhasePencil.phasePencil_7_1 N hN _ _ _ _).mpr (h k).2⟩) i j hij
    have hp : SupportedOnParity (plusContraction i j hij s f) 0 := by
      intro x hx
      rw [plusContraction_apply] at hx
      have hn : f (extendBits i j hij x false false) ≠ 0 ∨
          f (extendBits i j hij x true true) ≠ 0 := by
        by_contra hn
        push Not at hn
        exact hx (by simp [hn])
      rcases hn with hn | hn
      · simpa only [parity_extend_equal] using heven _ hn
      · simpa only [parity_extend_equal] using heven _ hn
    refine ⟨hp,?_⟩
    have hcard : Fintype.card (Remaining i j) = 2 := by
      have hh := remaining_card i j hij
      simp only [Fintype.card_fin] at hh
      omega
    have hzero : RootComplement N (plusContraction i j hij s f (fun _ => false))
        (plusContraction i j hij s f (fun _ => true)) := by
      have hc := (provedPhasePencil.phasePencil_7_1 N hN _ _ _ _).mp hr s hs
      rw [← extendBits_flipRemaining i j hij (fun _ => false),
        ← extendBits_flipPair i j hij (fun _ => false)] at hc
      have hz : restrict i j (fun _ => false) = fun _ => false := rfl
      have ht : restrict i j (fun _ => true) = fun _ => true := rfl
      have ef := extendBits_restrict i j hij (fun _ => false)
      have et := extendBits_restrict i j hij (fun _ => true)
      rw [hz] at ef
      rw [ht] at et
      apply (safe_pair_iff _ _ _).mp
      simpa only [plusContraction_apply,hz,Bool.not_false,ef,et] using hc
    intro x
    by_cases hx : parity x = 0
    · rcases even_two_constant hcard x hx with rfl | rfl
      · exact hzero
      · exact RootComplement.reverse (by omega) hzero
    · exact Or.inl ⟨by by_contra hn; exact hx (hp x hn),
        by by_contra hn; exact hx ((parity_complement_two hcard x).symm.trans (hp _ hn))⟩

theorem source_5_12 {N : ℕ} (hN : 3 ≤ N) (f : Signature AlgebraicComplex 4)
    (heven : SupportedOnParity f 0) :
    CyclicContractions N f ↔
      CyclicNormalForm N (f (fun _ => false)) (f (fun _ => true))
        (fun i => f (centralWord i (fun _ => false)))
        (fun i => f (flipAll (centralWord i (fun _ => false)))) :=
  (cyclic_local_iff hN f heven).trans (cyclic_pencils_iff_normalForm hN _ _ _ _)

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity
