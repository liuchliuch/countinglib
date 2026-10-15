import ComplexCSP.Structure.MaltsevCSPCode
import ComplexCSP.Recognition.GlobalConditions
import ComplexCSP.Instances.ValueTransport
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {D K ι : Type} [Fintype D] [CommSemiring K]
theorem language_value_generated (L : Language D K ι) (i : ι) : Instance.Generated L (L.value i) := by
  let I : Instance L (Fin (L.arity i)) (Fin 0) := ⟨[⟨i, Sum.inl⟩]⟩
  refine ⟨0, I, ?_⟩
  intro a
  simp [I, Instance.partition, Instance.eval, Constraint.eval, Function.comp_def]
theorem common_support_preserves_table (L : Language D K ι)
    {m : Operation D} (hm : CommonPolymorphism (generatedSupports L) m) (i : ι) :
    Preserves m {x | L.value i x ≠ 0} := by
  let R : Relation D := ⟨L.arity i, {x | L.value i x ≠ 0}⟩
  exact hm R ⟨L.value i, language_value_generated L i, rfl⟩
section Field
variable {F : Type} [Field F] [DecidableEq F] {d s : ℕ} [Nonempty (Fin d)]
omit [DecidableEq F] in
theorem exists_support_operation_of_jointBO (L : Language (Fin d) F (Fin s))
    (σ : F →+* ℂ) (hBO : JointBO (L.mapValues σ)) :
    ∃ m : Operation (Fin d), IsMaltsev m ∧ ∀ i, Preserves m {x | L.value i x ≠ 0} := by
  obtain ⟨m, hm, hcommon⟩ := hBO.common_support_maltsev (L.mapValues σ)
  refine ⟨m, hm, ?_⟩
  intro i
  have h := common_support_preserves_table (L.mapValues σ) hcommon i
  simpa [Language.mapValues] using h
theorem jointBO_raw_support_compiler (L : Language (Fin d) F (Fin s))
    (σ : F →+* ℂ) (hBO : JointBO (L.mapValues σ)) (defaultValue : Fin d) :
    ∃ m : Operation (Fin d), IsMaltsev m ∧
      ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g),
        Correct (rawSupportWitness L m defaultValue g hg).toCode {x | ComplexityCSPCode.eval L g x ≠ 0} := by
  obtain ⟨m, hm, hL⟩ := exists_support_operation_of_jointBO L σ hBO
  exact ⟨m, hm, fun g hg => rawSupportWitness_correct L hm hL defaultValue g hg⟩
end Field
end ComplexCSP.MaltsevWitness
