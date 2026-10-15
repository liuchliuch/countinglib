import Paper2.SourceFaithful.SourceStatements.PhaseProductParityDeck
import Paper2.HeightOne.Dihedral.QuaternaryPrime

/-! The one- and two-complementary-pair forms in source Proposition 5.13,
with literal even-block partition witnesses for P_N. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards

def DihedralNormalForm (N : ℕ) (f : Signature AlgebraicComplex 4) : Prop :=
  ∃ (a : Word4) (p : AlgebraicComplex), p ≠ 0 ∧
    ((∃ δ, Root N δ ∧ f = fun x => p * twoPoint a δ x) ∨
      ∃ (i : Fin 3) (γ δ : AlgebraicComplex), Root N γ ∧ Root N δ ∧
        f = blockProduct i a p (-γ) (-δ / γ))

lemma phaseRatio_two {N : ℕ} (hN : 0 < N) {r : AlgebraicComplex} (hr : Root N r) :
    PhaseRatio N 2 r := by
  let u : AlgebraicComplexˣ := Units.mk0 r (root_ne_zero hN hr)
  let s : rootsOfUnity N AlgebraicComplex := ⟨u,by
    rw [mem_rootsOfUnity]
    apply Units.ext
    simpa [u,Root] using hr⟩
  refine ⟨s,?_⟩
  change r = (-1 : AlgebraicComplex) ^ 2 * r
  norm_num

lemma phaseRatio_one_negative {N : ℕ} (hN : 0 < N) {r : AlgebraicComplex} (hr : Root N r) :
    PhaseRatio N 1 (-r) := by
  let u : AlgebraicComplexˣ := Units.mk0 r (root_ne_zero hN hr)
  let s : rootsOfUnity N AlgebraicComplex := ⟨u,by
    rw [mem_rootsOfUnity]
    apply Units.ext
    simpa [u,Root] using hr⟩
  refine ⟨s,?_⟩
  change -r = (-1 : AlgebraicComplex) ^ 1 * r
  ring

lemma phaseProduct_twoPoint {N : ℕ} (hN : 0 < N) (a : Word4) (r : AlgebraicComplex)
    (hr : Root N r) : PhaseProduct N (twoPoint a r) := by
  exact PhaseProduct.of_block ⟨1,a,r,rfl,phaseRatio_two hN hr,rfl⟩

lemma phaseProduct_blockProduct {N : ℕ} (hN : 0 < N) (i : Fin 3) (a : Word4)
    (p α β : AlgebraicComplex) (hα : Root N α) (hβ : Root N β) :
    PhaseProduct N (blockProduct i a p (-α) (-β)) := by
  have hA : PhaseProduct N (twoPoint (a ∘ firstPorts i) (-α)) :=
    PhaseProduct.of_block ⟨0,a ∘ firstPorts i,-α,rfl,phaseRatio_one_negative hN hα,rfl⟩
  have hB : PhaseProduct N (twoPoint (a ∘ secondPorts i) (-β)) :=
    PhaseProduct.of_block ⟨0,a ∘ secondPorts i,-β,rfl,phaseRatio_one_negative hN hβ,rfl⟩
  have h := ((hA.tensor hB).reindex
    ((finSumFinEquiv : Fin 2 ⊕ Fin 2 ≃ Fin 4).trans (blockPorts i))).scale p
  convert h using 1
  funext x
  simp only [Pi.smul_apply,smul_eq_mul,Tensor.reindex_apply,Tensor.tensor_apply,
    Equiv.trans_apply,finSumFinEquiv_apply_left,finSumFinEquiv_apply_right,
    blockProduct,Function.comp_def,mul_assoc]
  congr 1
  congr 1 <;> congr 1 <;> funext j <;> fin_cases i <;> fin_cases j <;> rfl

theorem dihedral_normalForm_phaseProduct {N : ℕ} (hN : 0 < N)
    {f : Signature AlgebraicComplex 4} (h : DihedralNormalForm N f) :
    PhaseProduct N f := by
  obtain ⟨a,p,_,⟨δ,hδ,rfl⟩ | ⟨i,γ,δ,hγ,hδ,rfl⟩⟩ := h
  · exact (phaseProduct_twoPoint hN a δ hδ).scale p
  · have hd : -δ / γ = -(δ / γ) := by ring
    rw [hd]
    exact phaseProduct_blockProduct hN i a p γ (δ / γ) hγ (root_div hδ hγ)

theorem local_dihedral_normalForm {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (f : Signature AlgebraicComplex 4) (hf : f ≠ 0)
    (h : DihedralContractions N f) : DihedralNormalForm N f := by
  classical
  obtain ⟨hp,hd⟩ := (local_dihedral_iff hN f).mp h
  obtain ⟨a,ha⟩ : ∃ a, f a ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hf (funext hn)
  refine ⟨a,f a,ha,?_⟩
  obtain ⟨_,⟨r,hr,ht⟩,hs | ⟨i,α,β,hα,hβ,hx,hy,hti,hs⟩⟩ :=
    fullDeck_support_pairs hodd hp hd a ha
  · exact Or.inl ⟨r,hr,twoPoint_of_one_pair f a r ht hs⟩
  · refine Or.inr ⟨i,α,α * β,hα,root_mul hα hβ,?_⟩
    have hα0 := root_ne_zero hodd.pos hα
    have he : -(α * β) / α = -β := by field_simp
    rw [he]
    exact blockProduct_of_values f i a (f a) (-α) (-β) rfl hx hy
      (by simpa using hti) hs

theorem source_5_13_phaseProduct {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (f : Signature AlgebraicComplex 4) (h : DihedralContractions N f) :
    PhaseProduct N f := by
  by_cases hf : f = 0
  · rw [hf]; exact PhaseProduct.zero N _
  · exact dihedral_normalForm_phaseProduct (by omega)
      (local_dihedral_normalForm hN hodd f hf h)

theorem source_5_13_prime_forward {N : ℕ} (hN : 3 ≤ N) (hodd : Odd N)
    (f : Signature AlgebraicComplex 4) (hp : TensorPrime f)
    (h : DihedralContractions N f) :
    ∃ (a : Word4) (p δ : AlgebraicComplex), p ≠ 0 ∧ Root N δ ∧
      f = fun x => p * twoPoint a δ x := by
  obtain ⟨hpar,hdeck⟩ := (local_dihedral_iff hN f).mp h
  exact tensorPrime_fullDeck_twoPoint hodd f hp hpar hdeck

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity
