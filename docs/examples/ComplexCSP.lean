import Counting.Flagships.ComplexCSP

/-!
# A positive-arity weighted CSP and the closed classification theorem

The fixed language has Boolean domain `Fin 2`, one binary signature, and weight
2 on every tuple. Repeated occurrences contribute repeated factors of 2;
hidden variables are still summed even when they are isolated. Its generated
tables are constant, so their legally purified rows are equal and satisfy the
literal joint Block Orthogonality condition.

We then apply structural collapse and the fixed-language complexity endpoint.
The evaluator returns rational-basis coordinates under the original canonical
instance promise. This does not assert a uniform polynomial-time recognizer or
natural-valued #P membership for general complex-weighted CSPs.
-/

namespace Counting.Tutorial.ComplexCSP

open _root_.ComplexCSP
open _root_.ComplexCSP.BlockOrthogonality _root_.ComplexCSP.RowTypes
open _root_.ComplexCSP.Purification.PurificationMap

noncomputable section

/-- Both arity and its positivity proof are part of the actual language data. -/
def rationalLanguage : Language (Fin 2) ℚ (Fin 1) where
  arity := fun _ => 2
  arity_pos := fun _ => by decide
  value := fun _ _ => 2

/-- The complex interpretation uses the fixed rational field embedding. -/
def complexLanguage : Language (Fin 2) ℂ (Fin 1) :=
  rationalLanguage.mapValues (algebraMap ℚ ℂ)

/-- The one-coordinate basis fixes the exact output representation. -/
def rationalBasis : Module.Basis (Fin 1) ℚ ℚ := Module.Basis.singleton (Fin 1) ℚ

theorem language_values_algebraic (i : Fin 1)
    (a : Fin (complexLanguage.arity i) → Fin 2) :
    IsAlgebraic ℚ (complexLanguage.value i a) := by
  change IsAlgebraic ℚ (2 : ℂ)
  exact isAlgebraic_natCast 2

/-- Every occurrence contributes its own factor, irrespective of its scope. -/
theorem evaluation_formula {B H : Type} (I : Instance complexLanguage B H)
    (a : B → Fin 2) (b : H → Fin 2) :
    I.eval a b = (2 : ℂ) ^ I.constraints.length := by
  simp [Instance.eval, Constraint.eval, complexLanguage, rationalLanguage,
    Language.mapValues]

/-- Summation retains all hidden-variable assignments, including isolated ones. -/
theorem partition_formula {B H : Type} [Fintype H] [DecidableEq H]
    (I : Instance complexLanguage B H) (a : B → Fin 2) :
    I.partition a = (Fintype.card (H → Fin 2) : ℂ) *
      (2 : ℂ) ^ I.constraints.length := by
  simp [Instance.partition, evaluation_formula]

/-- Two equal constraint occurrences use the same variable twice. The second
hidden variable is isolated, but still has two possible Boolean assignments. -/
def repeatedInstance : Instance complexLanguage (Fin 0) (Fin 2) where
  constraints :=
    [⟨0, fun _ => Sum.inr 0⟩, ⟨0, fun _ => Sum.inr 0⟩]

/-- Two occurrences contribute 4, and two hidden variables contribute 4. -/
theorem repeated_instance_partition :
    repeatedInstance.partition Fin.elim0 = (16 : ℂ) := by
  rw [partition_formula]
  norm_num [repeatedInstance, Fintype.card_fun]

/-- Generated tables do not depend on their retained assignment. -/
theorem generated_table_constant {B : Type} {G : (B → Fin 2) → ℂ}
    (hG : Instance.Generated complexLanguage G) (a b : B → Fin 2) : G a = G b := by
  obtain ⟨n, I, hI⟩ := hG
  rw [← hI a, ← hI b, partition_formula, partition_formula]

/-- Equal source entries have equal encodings in the intrinsic entry group. -/
theorem encodeTable_eq_of_entry_eq {X D : Type} (G : X → D → ℂ)
    (x y : X) (z : D) (h : G x z = G y z) :
    encodeTable G x z = encodeTable G y z := by
  classical
  by_cases hx : G x z = 0
  · have hy : G y z = 0 := h.symm.trans hx
    simp [encodeTable, hx, hy]
  · have hy : G y z ≠ 0 := fun hy => hx (h.trans hy)
    simp only [encodeTable, dite_eq_right hx, dite_eq_right hy]
    congr 2
    apply Units.ext
    exact h

/-- Joint purification preserves row equality of every generated table. -/
theorem generated_joint_rows_equal {n : ℕ} (Ts : Fin n → PositiveTable (Fin 2))
    (hTs : ∀ i, Instance.Generated complexLanguage (Ts i).value)
    (i : Fin n) (x y : Fin (Ts i).rowArity → Fin 2) :
    jointRows (Fin 2) Ts i x = jointRows (Fin 2) Ts i y := by
  funext z
  unfold jointRows PositiveTable.purifiedRows purifyTable
  simp only [Function.comp_apply]
  apply congrArg _
  apply encodeTable_eq_of_entry_eq
  exact generated_table_constant (hTs i) _ _

/-- Prove the full joint condition, rather than assuming the classifier's answer. -/
theorem language_jointBO : JointBO complexLanguage := by
  intro n _ Ts _ hTs i _
  have he := generated_joint_rows_equal Ts hTs i
  constructor
  · intro x y _ _
    left
    refine ⟨1, by norm_num, ?_⟩
    intro z
    rw [he x y]
    simp
  · intro x y _ _ _
    left
    rw [he x y]
    exact proportional_refl _

/-- The flagship collapse theorem supplies the global type partition and one
common Mal'tsev operation for the entire unbounded generated family. -/
theorem language_caiChenConditions : CaiChenConditions complexLanguage :=
  (Counting.ComplexCSP.structural_collapse complexLanguage
    language_values_algebraic).mpr language_jointBO

/-- The closed classification endpoint gives a polynomial-time finite-machine
evaluator for this fixed rational language and this exact coordinate codec. -/
theorem fixed_language_inFP :
    (ComplexityCSPCountReduction.partitionProblem rationalLanguage rationalBasis).InFP := by
  exact (ComplexityClassification.ordinary_jointBO rationalLanguage rationalBasis
    (algebraMap ℚ ℂ)).1 language_jointBO

end

end Counting.Tutorial.ComplexCSP
