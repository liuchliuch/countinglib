import ComplexCSP.Algebra.EncodedNumberFieldPresentation

/-!
# The genuine complex embedding of a checked raw integer-tail field

Only the successful irreducibility check and an actual complex root are supplied.
The own-field power basis and its proved minimal polynomial construct the
embedding. The complex numbers are not assumed to be a number field.
This is semantic proof-level code; arithmetic continues on rational vectors.
-/

namespace ComplexCSP.RawTailComplexEmbedding

open Polynomial EncodedNumberField
open scoped BigOperators

variable {n : ℕ} (a : Fin n → ℤ)

/-- Native polynomial notation is confined to the semantic contract. -/
noncomputable def polynomial : Polynomial ℤ :=
  MonicIrreducibility.denote (MonicIrreducibility.fromTail a)

variable [Fact (Element.Valid n (EffectiveRoots.coefficientRelation a))]

abbrev Field := Element n (EffectiveRoots.coefficientRelation a)

/-- The validated integer polynomial is the own generator's rational minimal
polynomial, by actual irreducibility and the proved reduction relation. -/
theorem polynomial_map_eq_minpoly (ha : MonicIrreducibility.irreducibleMonicTail a = true) :
    (polynomial a).map (Int.castRingHom ℚ) = minpoly ℚ (Element.generator
      (c := EffectiveRoots.coefficientRelation a)) := by
  have hp : (polynomial a).Monic := MonicIrreducibility.denote_monic _
    (MonicIrreducibility.fromTail_leading a)
  have hi : Irreducible ((polynomial a).map (Int.castRingHom ℚ)) :=
    (MonicIrreducibility.irreducibleMonicTail_correct a).mp ha
  apply minpoly.eq_of_irreducible_of_monic hi _ (hp.map _)
  change aeval (Element.generator (c := EffectiveRoots.coefficientRelation a))
    ((polynomial a).map (algebraMap ℤ ℚ)) = 0
  rw [aeval_map_algebraMap]
  exact Element.checkedTail_integer_root a

private theorem minpoly_root (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (α : ℂ) (hα : aeval α (polynomial a) = 0) :
    aeval α (minpoly ℚ (Element.generator (c := EffectiveRoots.coefficientRelation a))) = 0 := by
  rw [← polynomial_map_eq_minpoly a ha]
  change aeval α ((polynomial a).map (algebraMap ℤ ℚ)) = 0
  rw [aeval_map_algebraMap]
  exact hα

/-- The actual rational-algebra embedding induced by the designated complex root. -/
noncomputable def algHom (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (α : ℂ) (hα : aeval α (polynomial a) = 0) : Field a →ₐ[ℚ] ℂ :=
  (Element.powerBasis (n := n) (c := EffectiveRoots.coefficientRelation a)).lift α
    (minpoly_root a ha α hα)

/-- The requested genuine ring embedding, with no caller-supplied abstract model. -/
noncomputable def embedding (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (α : ℂ) (hα : aeval α (polynomial a) = 0) : Field a →+* ℂ :=
  (algHom a ha α hα).toRingHom

@[simp] theorem embedding_generator
    (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (α : ℂ) (hα : aeval α (polynomial a) = 0) :
    embedding a ha α hα (Element.generator (c := EffectiveRoots.coefficientRelation a)) = α :=
  PowerBasis.lift_gen _ α (minpoly_root a ha α hα)

/-- Every stored rational coefficient vector is interpreted exactly at the
specified complex root. -/
theorem embedding_apply (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (α : ℂ) (hα : aeval α (polynomial a) = 0) (x : Field a) :
    embedding a ha α hα x = interpret α x.coeff := by
  calc
    embedding a ha α hα x = embedding a ha α hα
        (interpret (Element.generator (c := EffectiveRoots.coefficientRelation a)) x.coeff) := by
      rw [Element.interpret_generator]
    _ = interpret (embedding a ha α hα
        (Element.generator (c := EffectiveRoots.coefficientRelation a))) x.coeff :=
      Element.map_interpret_complex _ _ _
    _ = interpret α x.coeff := by rw [embedding_generator]

theorem embedding_mk (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (α : ℂ) (hα : aeval α (polynomial a) = 0) (v : CoeffVector n) :
    embedding a ha α hα (⟨v⟩ : Field a) = interpret α v :=
  embedding_apply a ha α hα ⟨v⟩

theorem embedding_injective (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (α : ℂ) (hα : aeval α (polynomial a) = 0) :
    Function.Injective (embedding a ha α hα) := (embedding a ha α hα).injective

omit [Fact (Element.Valid n (EffectiveRoots.coefficientRelation a))] in
/-- Direct sum-reduction input implies the native polynomial root contract. -/
theorem polynomial_root_of_relation (α : ℂ)
    (hα : α ^ n = interpret α (EffectiveRoots.coefficientRelation a)) :
    aeval α (polynomial a) = 0 := by
  have hp : (polynomial a).Monic := MonicIrreducibility.denote_monic _
    (MonicIrreducibility.fromTail_leading a)
  have hd : (polynomial a).natDegree = n := MonicIrreducibility.denote_natDegree _
    (MonicIrreducibility.fromTail_leading a)
  have htop : (polynomial a).coeff n = 1 := by simpa only [hd] using hp.coeff_natDegree
  have hcoeff (i : Fin n) : (polynomial a).coeff i.val = a i := by
    simp [polynomial, MonicIrreducibility.coefficient, MonicIrreducibility.fromTail,
      i.isLt, show i.val < n + 1 by omega]
  rw [aeval_eq_sum_range, hd, Finset.sum_range_succ, htop, one_smul, Finset.sum_range]
  simp only [hcoeff, zsmul_eq_mul]
  rw [hα]
  simp [interpret, EffectiveRoots.coefficientRelation, Finset.sum_neg_distrib]

/-- Equivalent entry point accepting only the direct raw-tail reduction equality. -/
noncomputable def embeddingOfRelation (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (α : ℂ) (hα : α ^ n = interpret α (EffectiveRoots.coefficientRelation a)) : Field a →+* ℂ :=
  embedding a ha α (polynomial_root_of_relation a α hα)

/-- A wrapper installs the field validity fact from the actual check result.
The caller does not provide a semantic model or a field-law witness. -/
noncomputable def checkedEmbedding (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (α : ℂ) (hα : aeval α (polynomial a) = 0) :
    letI : Fact (Element.Valid n (EffectiveRoots.coefficientRelation a)) :=
      ⟨Element.valid_of_irreducibleMonicTail a ha⟩
    Element n (EffectiveRoots.coefficientRelation a) →+* ℂ := by
  letI : Fact (Element.Valid n (EffectiveRoots.coefficientRelation a)) :=
    ⟨Element.valid_of_irreducibleMonicTail a ha⟩
  exact embedding a ha α hα

/-- Checked wrapper for the direct sum-reduction input contract. -/
noncomputable def checkedEmbeddingOfRelation
    (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (α : ℂ) (hα : α ^ n = interpret α (EffectiveRoots.coefficientRelation a)) :
    letI : Fact (Element.Valid n (EffectiveRoots.coefficientRelation a)) :=
      ⟨Element.valid_of_irreducibleMonicTail a ha⟩
    Element n (EffectiveRoots.coefficientRelation a) →+* ℂ := by
  letI : Fact (Element.Valid n (EffectiveRoots.coefficientRelation a)) :=
    ⟨Element.valid_of_irreducibleMonicTail a ha⟩
  exact embeddingOfRelation a ha α hα

end ComplexCSP.RawTailComplexEmbedding
