import Paper2.HeightOne.GroupSplit.ActualTransfers
import Paper2.HeightOne.GroupSplit.FieldMap
import Paper2.HeightOne.GroupSplit.FiniteCases
import Paper2.Tractable.CommonTransform
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! Explicit, named Paper 1 boundary. Only the cited classification's group-type
conclusion and the cited bounded-torsion finiteness conclusion are consumed.
No Paper 2 theorem, normalizing basis, or actual representative is accepted. -/
namespace Paper2.HeightOne.GroupSplit
open MatrixGroup Tractable
noncomputable section

/-- The five abstract group types from Paper 1 Proposition 2.1. This is only
used group-theoretically; it cannot provide a legal signature basis. -/
def FinitePGLTypes (A : Type*) [Group A] : Prop :=
  IsCyclic A ∨
  (∃ m : ℕ, 2 ≤ m ∧ Nonempty (A ≃* DihedralGroup m)) ∨
  Nonempty (A ≃* A4) ∨ Nonempty (A ≃* S4) ∨ Nonempty (A ≃* A5)

/-- Exact source clauses actually consumed. Both are transparent parameters.
The second is the source's finite projective image after its canonical field
inclusion, with every signature entry in the one fixed number field. -/
structure Paper1Accepted : Prop where
  finitePGLTypes_2_1 : ∀ H : Subgroup (PGL2 ℂ), Finite H → FinitePGLTypes H
  boundedTorsion_5_2 :
    ∀ (L : IntermediateField ℚ AlgebraicComplex), FiniteDimensional ℚ L →
    ∀ (F : SignatureFamily AlgebraicComplex),
      (∀ f ∈ F, ∀ x, f.2 x ∈ L) →
      (actualTransfers F).Nonempty →
      (∀ B, ActualNonsingular F B → ProjectivelyFinite (transfer B)) →
      (projectiveClass '' actualTransfers F).Finite

lemma FinitePGLTypes.of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (h : FinitePGLTypes B) : FinitePGLTypes A := by
  unfold FinitePGLTypes at h ⊢
  rcases h with h | h | h | h | h
  · exact Or.inl (e.isCyclic.mpr h)
  · obtain ⟨m, hm, ⟨em⟩⟩ := h
    exact Or.inr (Or.inl ⟨m, hm, ⟨e.trans em⟩⟩)
  · obtain ⟨e4⟩ := h
    exact Or.inr (Or.inr (Or.inl ⟨e.trans e4⟩))
  · obtain ⟨es⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans es⟩)))
  · obtain ⟨e5⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e5⟩)))

/-- Applying the complex classification after a faithful inclusion of fields
preserves the abstract group type. The image's conjugator is never used. -/
theorem finitePGLTypes_algebraic (P1 : Paper1Accepted)
    (H : Subgroup (PGL2 AlgebraicComplex)) (hH : Finite H) : FinitePGLTypes H := by
  let f : AlgebraicComplex →+* ℂ := AlgebraicComplex.subtype
  let e := subgroupFieldMapEquiv f H
  letI : Finite H := hH
  have hi : Finite (H.map (pglMap f)) := Finite.of_equiv H e.toEquiv
  exact FinitePGLTypes.of_equiv e (P1.finitePGLTypes_2_1 _ hi)

end
end Paper2.HeightOne.GroupSplit
