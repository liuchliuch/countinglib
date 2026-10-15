import Paper2.FixedFieldOutput.LinearMachines

/-! Actual transitions between canonical vector answers and field-semantic
arithmetic specifications. Both codes are literal canonical rational vectors;
these reinterpretations add no runtime algebraic decoder. -/
namespace Paper2.FixedFieldOutput
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines Paper2.Algebraic
open Paper2.ExactInput Paper2.Problem Paper2.Tractable
noncomputable section

 def toField (source target : Language) (v : Answer source) : target.coefficientField :=
  target.fieldPresentation.decode (conversion source target v)

 def toFieldComputes (source target : Language) :
    Computes (answerEncoding source) target.fieldPresentation.encoding (toField source target) :=
  recode (conversionComputes source target) id (fun _ => rfl)
    (fun v => (target.fieldPresentation.encoding_decode _).symm)

 def fromFieldComputes (L : Language) :
    Computes L.fieldPresentation.encoding (answerEncoding L) L.fieldPresentation.basis.equivFun :=
  recode (identityComputes (answerEncoding L)) L.fieldPresentation.basis.equivFun
    (fun _ => rfl) (fun _ => rfl)

 theorem toField_correct (source target : Language) (v : Answer source)
    (y : target.coefficientField)
    (h : (source.fieldPresentation.decode v : AlgebraicComplex) = (y : AlgebraicComplex)) :
    toField source target v = y := by
  unfold toField
  rw [conversion_correct source target v (target.fieldPresentation.basis.equivFun y)]
  · exact target.fieldPresentation.basis.equivFun.symm_apply_apply y
  · rw [show target.fieldPresentation.decode
      (target.fieldPresentation.basis.equivFun y) = y from
        target.fieldPresentation.basis.equivFun.symm_apply_apply y]
    exact h

 theorem toField_answer (w : Wiring) (source target : Language) (G : Instance source)
    (y : target.coefficientField) (h : value w source G = (y : AlgebraicComplex)) :
    toField source target (answer w source G) = y :=
  toField_correct source target _ y ((answer_correct w source G).trans h)

end
end Paper2.FixedFieldOutput
