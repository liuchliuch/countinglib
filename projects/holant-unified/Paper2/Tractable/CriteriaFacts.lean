import Paper2.Tractable.Criteria

/-! Checked boundary cases of the literal seven-clause predicate. These are
structural facts; graph evaluation still retains nullary factors and zero vertices. -/
namespace Paper2.Tractable

@[simp] theorem preprocess_empty : preprocess ∅ = ∅ := by
  ext f
  simp [preprocess]

@[simp] theorem tract_empty : Tract ∅ := by
  refine ⟨?_, ?_⟩
  · simp
  · rw [preprocess_empty]
    exact Or.inr (Or.inr (Or.inl (by intro f hf; exact False.elim hf)))

@[simp] theorem tract_preprocess (F : SignatureFamily AlgebraicComplex) :
    Tract (preprocess F) ↔ Tract F := by simp only [Tract, preprocess_idempotent]

theorem preprocess_insert_zero (F : SignatureFamily AlgebraicComplex) (n : ℕ) :
    preprocess (insert (⟨n, 0⟩ : AnySignature AlgebraicComplex) F) = preprocess F := by
  ext f
  constructor
  · rintro ⟨hf, hn, hz⟩
    rcases hf with h | h
    · subst f
      exact False.elim (hz rfl)
    · exact ⟨h, hn, hz⟩
  · rintro ⟨h, hn, hz⟩
    exact ⟨Or.inr h, hn, hz⟩

theorem preprocess_insert_nullary (F : SignatureFamily AlgebraicComplex)
    (f : Signature AlgebraicComplex 0) :
    preprocess (insert (⟨0, f⟩ : AnySignature AlgebraicComplex) F) = preprocess F := by
  ext g
  constructor
  · rintro ⟨hg, hn, hz⟩
    rcases hg with h | h
    · subst g
      exact False.elim (Nat.lt_irrefl 0 hn)
    · exact ⟨h, hn, hz⟩
  · rintro ⟨h, hn, hz⟩
    exact ⟨Or.inr h, hn, hz⟩

@[simp] theorem tract_insert_zero (F : SignatureFamily AlgebraicComplex) (n : ℕ) :
    Tract (insert (⟨n, 0⟩ : AnySignature AlgebraicComplex) F) ↔ Tract F := by
  simp only [Tract, preprocess_insert_zero]

@[simp] theorem tract_insert_nullary (F : SignatureFamily AlgebraicComplex)
    (f : Signature AlgebraicComplex 0) :
    Tract (insert (⟨0, f⟩ : AnySignature AlgebraicComplex) F) ↔ Tract F := by
  simp only [Tract, preprocess_insert_nullary]

/-- A finite family is not required to be preprocessed before using Tract. -/
theorem tract_iff_core_of_finite (F : SignatureFamily AlgebraicComplex) (hF : F.Finite) :
    Tract F ↔ TractCore (preprocess F) :=
  ⟨And.right, fun h => ⟨hF.subset (fun _ hf => hf.1), h⟩⟩

end Paper2.Tractable
