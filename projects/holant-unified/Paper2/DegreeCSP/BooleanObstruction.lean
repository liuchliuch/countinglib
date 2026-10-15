import Paper2.DegreeCSP.GeneratedOrthogonality
import Paper2.DegreeCSP.TwoRowRestriction
import Paper2.DegreeCSP.BinaryTractOrthogonality

/-! A failed literal block-orthogonality condition has an actual two-row
degree-generated witness. The coefficients, hidden-variable sum, and degree
promise are retained by the row selector. -/
namespace Paper2.DegreeCSP.BooleanObstruction
open OriginalBO Tractable TensorDecomposition
noncomputable section

def pairRows {X J : Type} (G : X → J → ℂ) (a b : X) : Bool → J → ℂ :=
  fun s => if s then G b else G a

theorem blockOrthogonal_iff_pairRows {X J : Type} [Fintype J]
    (G : X → J → ℂ) :
    BlockOrthogonal G ↔ ∀ a b, BlockOrthogonal (pairRows G a b) := by
  constructor
  · intro h a b
    have hp := precompose_rows h (fun s : Bool => if s then b else a)
    convert hp using 1
    funext s j
    cases s <;> rfl
  · intro h
    refine ⟨fun a b ha hb => ?_,fun a b ha hb hm => ?_⟩
    · simpa only [pairRows,Bool.false_eq_true,ite_false,ite_true]
        using (h a b).1 false true ha hb
    · simpa only [pairRows,Bool.false_eq_true,ite_false,ite_true]
        using (h a b).2 false true ha hb hm

theorem exists_bad_pairRows {X J : Type} [Fintype J] (G : X → J → ℂ)
    (h : ¬BlockOrthogonal G) : ∃ a b, ¬BlockOrthogonal (pairRows G a b) := by
  classical
  by_contra hn
  apply h
  apply (blockOrthogonal_iff_pairRows G).mpr
  push Not at hn
  exact hn

theorem twoRow_table {n : ℕ} (f : Signature AlgebraicComplex (n+1))
    (a b : Fin n → Bool) :
    (fun s t : Bool => (TwoRowRestriction.twoRow f a b ![s,t] : ℂ)) =
      pairRows (tableRows f) a b := by
  funext s t
  cases s <;> simp [TwoRowRestriction.twoRow,pairRows,tableRows]

/-- An actual bad degree-generated table yields an actual bad binary table,
using only literal unit pins and disequality in the same source family. -/
theorem exists_bad_binary_generated {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hk : 0 < k)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h : ¬AllGeneratedOriginalBO F k) :
    ∃ g : Signature AlgebraicComplex 2,
      Generated F k g ∧ ¬BlockOrthogonal (fun s t : Bool => (g ![s,t] : ℂ)) := by
  classical
  simp only [AllGeneratedOriginalBO,not_forall,not_imp] at h
  obtain ⟨n,f,hf,hbad⟩ := h
  obtain ⟨a,b,hab⟩ := exists_bad_pairRows (tableRows f) hbad
  refine ⟨TwoRowRestriction.twoRow f a b,
    TwoRowRestriction.generated_twoRow hf hk h0 h1 hX a b,?_⟩
  rwa [twoRow_table]

/-- The obstruction is outside both actual binary tractable classes. -/
theorem exists_nontractable_binary_generated {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (hk : 0 < k)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h : ¬AllGeneratedOriginalBO F k) :
    ∃ g : Signature AlgebraicComplex 2, Generated F k g ∧ ¬Affine g ∧ ¬Product g := by
  obtain ⟨g,hg,hbad⟩ := exists_bad_binary_generated hk h0 h1 hX h
  obtain ⟨ha,hp⟩ := BinaryTractOrthogonality.not_binary_tract_of_not_bo g hbad
  exact ⟨g,hg,ha,hp⟩

end
end Paper2.DegreeCSP.BooleanObstruction
