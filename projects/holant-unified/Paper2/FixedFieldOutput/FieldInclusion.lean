import Paper2.FixedFieldOutput.FieldTransport

/-! Retained-language inclusion gives inclusion of the actual coefficient
fields. It validates the explicit fixed-matrix converter when target oracle
answers are lifted into a larger source field for arithmetic. -/
namespace Paper2.FixedFieldOutput
open Paper2.ExactInput Paper2.Problem Paper2.Tractable Paper2.Algebraic
noncomputable section

 theorem member_value_mem (L : Language) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family) (x : Fin n → Bool) :
    f x ∈ L.coefficientField := by
  obtain ⟨i,hi⟩ := hf
  have hn : L.arity i.val = n := congrArg Sigma.fst hi
  cases hn
  have he : L.signature i = f := eq_of_heq (Sigma.mk.inj_iff.mp hi).2
  rw [← he]
  exact L.signature_mem_field i x

 theorem coefficientField_mono (source target : Language)
    (h : source.family ⊆ target.family) : source.coefficientField ≤ target.coefficientField := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro _ ⟨a,rfl⟩
  exact member_value_mem target (source.signature a.1)
    (h ⟨a.1,rfl⟩) ((wordIndex (source.arity a.1.val)).symm a.2)

 theorem toField_coe (source target : Language)
    (h : source.family ⊆ target.family) (v : Answer source) :
    (toField source target v : AlgebraicComplex) = (source.fieldPresentation.decode v : AlgebraicComplex) := by
  let y : target.coefficientField :=
    ⟨source.fieldPresentation.decode v,coefficientField_mono source target h (source.fieldPresentation.decode v).property⟩
  have he := toField_correct source target v y rfl
  exact congrArg (fun a : target.coefficientField => (a : AlgebraicComplex)) he

 theorem toField_answer_coe (w : Wiring) (source target : Language)
    (h : source.family ⊆ target.family) (G : Instance source) :
    (toField source target (answer w source G) : AlgebraicComplex) = value w source G :=
  (toField_coe source target h _).trans (answer_correct w source G)

end
end Paper2.FixedFieldOutput
