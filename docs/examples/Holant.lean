import Counting.Flagships.Holant
import Paper2.ExactInput.Coverage

/-!
# A fixed weighted Boolean Holant language

The language contains the unary weight `[1, 2]` and binary equality. We exhibit
one-factor tensor decompositions, verify the arity-two structural branch, and
apply the closed ordinary-Holant evaluator theorem.

`Language.coverage_family` supplies valid exact algebraic input descriptors.
This is semantic coverage, not an executable encoder for arbitrary complex data.
The resulting FP theorem is for each supplied fixed descriptor language and uses
the original strict minimal-polynomial root output convention.
-/

namespace Counting.Tutorial.Holant

open Paper2 Paper2.Tractable Paper2.ExactInput

noncomputable section

/-- A nonconstant algebraic unary weight: false has weight 1, true has weight 2. -/
def weightedUnary : Signature AlgebraicComplex 1 := fun x => if x 0 then 2 else 1

/-- Binary equality uses two ordered ports. -/
def binaryEquality : Signature AlgebraicComplex 2 :=
  fun x => if x 0 = x 1 then 1 else 0

/-- One fixed finite family; no extra unary or pinning resources are added. -/
def family : SignatureFamily AlgebraicComplex :=
  {⟨1, weightedUnary⟩, ⟨2, binaryEquality⟩}

theorem family_finite : family.Finite := by
  exact (Set.finite_singleton _).insert _

/-- A signature is a tensor product of itself, with an explicit ordered port map. -/
theorem single_factor_tensor {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : n = 1 ∨ n = 2) :
    Signature.TensorClosure (fun m _ => m = 1 ∨ m = 2) f := by
  let D : TensorDecomposition AlgebraicComplex n :=
    { count := 1
      arity := fun _ => n
      factor := fun _ => f
      ports :=
        { toFun := fun p => p.2
          invFun := fun j => ⟨0, j⟩
          left_inv := by
            rintro ⟨i, j⟩
            have hi : i = 0 := Fin.eq_zero i
            subst i
            rfl
          right_inv := fun _ => rfl }
      scale := 1 }
  refine ⟨D, fun _ => hn, ?_⟩
  funext x
  simp [TensorDecomposition.value, D]

/-- The concrete language satisfies the third ordinary-Holant tractability clause. -/
theorem family_tractable : Tract family := by
  refine ⟨family_finite.subset (fun _ h => h.1), Or.inr (Or.inr (Or.inl ?_))⟩
  intro f hf
  have hm : f = ⟨1, weightedUnary⟩ ∨ f = ⟨2, binaryEquality⟩ := by
    simpa [family] using hf.1
  rcases hm with rfl | rfl
  · exact Or.inr (single_factor_tensor weightedUnary (Or.inl rfl))
  · exact Or.inr (single_factor_tensor binaryEquality (Or.inr rfl))

/-- Apply the flagship endpoint after proving its structural premise. The
language, field data, and polynomial bound are fixed before runtime instances. -/
theorem fixed_language_inFP (L : Language) (hL : L.family = family) :
    Paper2.Problem.InFP .ordinary L := by
  apply Counting.HolantUnified.FullDichotomy.ordinary_inFP L
  rw [hL]
  exact family_tractable

/-- The concrete weighted family has valid exact descriptors and an actual
polynomial-time ordinary-Holant evaluation machine. -/
theorem exact_language_and_evaluator :
    ∃ L : Language, L.family = family ∧ Paper2.Problem.InFP .ordinary L := by
  obtain ⟨L, hL⟩ := Language.coverage_family family family_finite
  exact ⟨L, hL, fixed_language_inFP L hL⟩

end

end Counting.Tutorial.Holant
