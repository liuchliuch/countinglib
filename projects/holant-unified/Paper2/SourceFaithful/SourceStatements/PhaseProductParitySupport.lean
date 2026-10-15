import Paper2.SourceFaithful.SourceStatements.PhaseProductParityForms

/-! The literal nonzero support and complementary-pair counts of the two
source Proposition 5.13 forms, in either Hamming parity. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards
attribute [local instance] Classical.propDecidable

def support (f : Signature AlgebraicComplex 4) : Finset Word4 :=
  Finset.univ.filter (fun x => f x ≠ 0)

def complementaryPairs (f : Signature AlgebraicComplex 4) : Finset (Finset Word4) :=
  (support f).image (fun a => {a,flipAll a})

lemma twoPoint_support (a : Word4) (p δ : AlgebraicComplex)
    (hp : p ≠ 0) (hδ : δ ≠ 0) :
    support (fun x => p * twoPoint a δ x) = {a,flipAll a} := by
  have hna := (sector_distinct 0 a).1
  change a ≠ (fun i => !(a i)) at hna
  change support (fun x => p * twoPoint a δ x) = {a,(fun i => !(a i))}
  ext x
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  by_cases hx : x = a
  · subst x
    simp_all [twoPoint,point]
  by_cases ht : x = fun i => !(a i)
  · subst x
    simp_all [twoPoint,point]
  · simp_all [twoPoint,point]

lemma blockProduct_support (i : Fin 3) (a : Word4) (p r s : AlgebraicComplex)
    (hp : p ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0) :
    support (blockProduct i a p r s) =
      {a,flipAll a,centralWord i a,flipAll (centralWord i a)} := by
  obtain ⟨h01,h02,h03,h12,h13,h23⟩ := sector_distinct i a
  ext x
  simp only [support,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_insert,Finset.mem_singleton]
  rw [blockProduct_expand]
  by_cases hxa : x = a
  · subst x; simp [point,h01,h02,h03,hp]
  by_cases hxt : x = flipAll a
  · subst x; simp [point,h01.symm,h12,h13,hp,hr,hs]
  by_cases hxx : x = centralWord i a
  · subst x; simp [point,h02.symm,h12.symm,h23,hp,hr]
  by_cases hxy : x = flipAll (centralWord i a)
  · subst x; simp [point,h03.symm,h13.symm,h23.symm,hp,hs]
  · simp [point,hxa,hxt,hxx,hxy]

theorem normalForm_pair_count {N : ℕ} (hN : 0 < N)
    {f : Signature AlgebraicComplex 4} (h : DihedralNormalForm N f) :
    (complementaryPairs f).card = 1 ∨ (complementaryPairs f).card = 2 := by
  obtain ⟨a,p,hp,⟨δ,hδ,rfl⟩ | ⟨i,γ,δ,hγ,hδ,rfl⟩⟩ := h
  · left
    rw [complementaryPairs,twoPoint_support a p δ hp (root_ne_zero hN hδ)]
    have geometry : ∀ a : Word4,
        (({a,flipAll a} : Finset Word4).image (fun x => ({x,flipAll x} : Finset Word4))).card = 1 := by decide
    exact geometry a
  · right
    rw [complementaryPairs,blockProduct_support i a p (-γ) (-δ / γ) hp
      (neg_ne_zero.mpr (root_ne_zero hN hγ))
      (div_ne_zero (neg_ne_zero.mpr (root_ne_zero hN hδ)) (root_ne_zero hN hγ))]
    have geometry : ∀ (i : Fin 3) (a : Word4),
        (({a,flipAll a,centralWord i a,flipAll (centralWord i a)} : Finset Word4).image
          (fun x => ({x,flipAll x} : Finset Word4))).card = 2 := by decide
    exact geometry i a

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity
