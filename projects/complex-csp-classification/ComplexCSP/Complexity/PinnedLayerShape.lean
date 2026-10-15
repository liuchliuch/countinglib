import ComplexCSP.Complexity.PinnedClassShape

/-! # Shape preservation of every raw capped layer

Even arbitrary caps and arbitrary operation tables produce the encoding of an
actual finite layer of the advertised dimension. This purely syntactic fact is
independent of ValidLayer and of all semantic correctness hypotheses.
-/
noncomputable section
namespace ComplexCSP.ComplexityPinnedLayer
open MaltsevWitness MaltsevRelations WeightedMaltsev ComplexityWitnessEncoding
open ComplexityWitnessPrimitives ComplexitySupportWitnessPrimitives ComplexityPinnedClass
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Operation (Fin d)) (space : Polynomial ℕ) (defaultValue : Fin d)

theorem split_shape (c : Context K d) : ∃ layer : WeightedMaltsev.Layer K d c.val.2.1,
    split L basis (ComplexityLabelExtension.curried m) space defaultValue c=encodeLayer layer := by
  choose U hU using (fun a : RowLabel K d =>
    ComplexityPinnedClass.build_shape_context L basis m space defaultValue c a)
  refine ⟨(labels L basis (ComplexityLabelExtension.curried m) space defaultValue c).map
    (fun a => (a,storeCode (U a))),?_⟩
  simp only [split,encodeLayer,List.map_map]
  apply List.map_congr_left
  intro a _
  unfold classRecord
  rw [hU]
  simp only [Function.comp_apply,packClass,encodeClass,encodeCode_store,storeCode]

theorem build_shape (c : Context K d) : ∃ layer : WeightedMaltsev.Layer K d (c.val.2.1-1),
    build L basis (ComplexityLabelExtension.curried m) space defaultValue c=encodeLayer layer :=
  split_shape L basis m space defaultValue (projectContext c)

end ComplexCSP.ComplexityPinnedLayer
