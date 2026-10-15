import Paper2.HeightOne.PhaseCards.FactorSaturation
import Paper2.Tractable.Conformal

/-! The source's least nonbinary prime arity is attached to literal retained
signatures, not an abstract counter that may change independently. -/
namespace Paper2.HeightOne
noncomputable section
open Tractable ExactInput PhaseCards

def HasNonbinaryPrime (F : SignatureFamily AlgebraicComplex) : Prop :=
  ∃ f ∈ F, TensorPrime f.2 ∧ 3 ≤ f.1

/-- The least arity comes with an actual retained prime realizing it. -/
def LeastPrimeArity (F : SignatureFamily AlgebraicComplex) (n : ℕ) : Prop :=
  (∃ f ∈ F, TensorPrime f.2 ∧ f.1 = n ∧ 3 ≤ n) ∧
    (∀ f ∈ F, TensorPrime f.2 → 3 ≤ f.1 → n ≤ f.1)

lemma exists_leastPrimeArity {F : SignatureFamily AlgebraicComplex}
    (hF : HasNonbinaryPrime F) : ∃ n, LeastPrimeArity F n := by
  classical
  have he : ∃ n, ∃ f ∈ F, TensorPrime f.2 ∧ f.1 = n ∧ 3 ≤ n := by
    obtain ⟨f, hf, hp, hn⟩ := hF
    exact ⟨f.1, f, hf, hp, rfl, hn⟩
  refine ⟨Nat.find he, Nat.find_spec he, ?_⟩
  intro f hf hp hn
  exact Nat.find_min' he ⟨f, hf, hp, rfl, hn⟩

lemma LeastPrimeArity.ge_three {F : SignatureFamily AlgebraicComplex} {n : ℕ}
    (h : LeastPrimeArity F n) : 3 ≤ n := by
  obtain ⟨f, hf, hp, harity, hn⟩ := h.1
  exact hn

lemma LeastPrimeArity.mono {F G : SignatureFamily AlgebraicComplex} {n m : ℕ}
    (hF : LeastPrimeArity F n) (hG : LeastPrimeArity G m) (hFG : F ⊆ G) : m ≤ n := by
  obtain ⟨f, hf, hp, rfl, hn⟩ := hF.1
  exact hG.2 f (hFG hf) hp hn

/-- No nonbinary prime leaves exactly the true unary/binary tensor closure,
including high-arity tensors with many factors. -/
lemma arityTwo_of_no_nonbinary (F : SignatureFamily AlgebraicComplex)
    (hfac : FactorClosed F) (hn : ¬ HasNonbinaryPrime F) : ArityTwoAlternative F := by
  intro f hf
  obtain ⟨D, hD, hpos, hprime, hmem⟩ := hfac f hf
  right
  refine ⟨D, ?_, hD⟩
  intro i
  have hlt : ¬ 3 ≤ D.arity i := fun hi => hn ⟨⟨D.arity i, D.factor i⟩, hmem i, hprime i, hi⟩
  have hp := hpos i
  omega

lemma tract_of_no_nonbinary (L : Language) (hfac : FactorClosed L.family)
    (hn : ¬ HasNonbinaryPrime L.family) : Tract (kImage L) := by
  have ht := Conformal.arityTwo_map sourceKBasis (arityTwo_of_no_nonbinary L.family hfac hn)
  refine ⟨(L.family_finite.image _).subset (fun f hf => hf.1), Or.inr (Or.inr (Or.inl ?_))⟩
  intro f hf
  exact ht f hf.1

/-- At the least nonbinary arity, every retained proper selected card factor
is binary once odd arities have been excluded. -/
lemma selected_card_factors_binary {F : SignatureFamily AlgebraicComplex} (M : BinaryMenu F)
    (L : Language) (heven : ∀ f ∈ L.family, Even f.1)
    {n : ℕ} (hmin : LeastPrimeArity L.family n)
    (f : AnySignature AlgebraicComplex) (hf : f.1 = n)
    (hprocessed : M.Processed f L)
    {g : AnySignature AlgebraicComplex} (hg : g ∈ M.children f) : g.1 = 2 := by
  have hp := M.child_arity hg
  have hmem := hprocessed.2.1 hg
  have he := heven g hmem
  have hlt : g.1 < n := by omega
  have hn : ¬ 3 ≤ g.1 := fun h => (not_le_of_gt hlt) (hmin.2 g hmem hp.2.1 h)
  obtain ⟨k, hk⟩ := he
  omega

end
end Paper2.HeightOne
