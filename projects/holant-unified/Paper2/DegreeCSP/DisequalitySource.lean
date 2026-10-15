import Paper2.DegreeCSP.FixedFieldReduction
import Paper2.DegreeCSP.NativeCompiler
import Paper2.Paper1ProvedGadgetProvider

/-! The degree-CSP source may use the literal binary disequality constraint.
An actual Eq_k graph constructs it, and the proved direct gadget compiler
removes this auxiliary vertex dictionary from the original native oracle. -/
namespace Paper2.DegreeCSP.DisequalitySource
open Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (L : Language) (k : ℕ) (hk : 3 ≤ k)
variable (heq : (⟨k,equality k⟩ : AnySignature AlgebraicComplex) ∈ L.family)

include k hk heq in
theorem adjoin : ∃ M : Language, M.family=sourceFamily L.family ∧
    FixedFieldOutput.Reduces .nativeX M L := by
  exact Paper1Proved.directGadgetProvider.adjoin_realizable L disequalityTable
    (disequality_realizable L.family k hk (member_realizable L.family (equality k) heq))

/-- This finite source dictionary is fixed before an instance is read. -/
def language : Language := Classical.choose (adjoin L k hk heq)

theorem family : (language L k hk heq).family=sourceFamily L.family :=
  (Classical.choose_spec (adjoin L k hk heq)).1

theorem back_exists : FixedFieldOutput.Reduces .nativeX (language L k hk heq) L :=
  (Classical.choose_spec (adjoin L k hk heq)).2

def back : LengthControlledOracleReduction
    (Problem.inputEncoding (language L k hk heq))
    (FixedFieldOutput.answerEncoding (language L k hk heq))
    (Problem.inputEncoding L) (FixedFieldOutput.answerEncoding L)
    (FixedFieldOutput.answer .nativeX (language L k hk heq))
    (FixedFieldOutput.answer .nativeX L) :=
  Classical.choice (back_exists L k hk heq)

theorem equality_index : ∃ i : Fin (language L k hk heq).count,
    (⟨(language L k hk heq).arity i.val,(language L k hk heq).signature i⟩ :
      AnySignature AlgebraicComplex)=⟨k,equality k⟩ := by
  have hm : (⟨k,equality k⟩ : AnySignature AlgebraicComplex) ∈ (language L k hk heq).family := by
    rw [family]
    exact Set.mem_insert_of_mem _ heq
  exact hm

def equalityLabel : Fin (language L k hk heq).count :=
  Classical.choose (equality_index L k hk heq)

theorem equalityLabel_signature :
    (⟨(language L k hk heq).arity (equalityLabel L k hk heq).val,
      (language L k hk heq).signature (equalityLabel L k hk heq)⟩ : AnySignature AlgebraicComplex)=
      ⟨k,equality k⟩ := Classical.choose_spec (equality_index L k hk heq)

/-- A literal degree-CSP instance with X constraints is compiled into valid
queries over the original target language, with every query length controlled. -/
def reduction : LengthControlledOracleReduction
    (FixedField.inputEncoding (language L k hk heq) k)
    (FixedFieldOutput.answerEncoding (language L k hk heq))
    (Problem.inputEncoding L) (FixedFieldOutput.answerEncoding L)
    (FixedField.sourceAnswer (language L k hk heq) k)
    (FixedFieldOutput.answer .nativeX L) :=
  (FixedField.reduction (language L k hk heq) k hk (equalityLabel L k hk heq)
    (equalityLabel_signature L k hk heq)).controlledCompose (back L k hk heq)

include hk heq in
theorem hardness_transport (hard : FixedField.SharpPHard (language L k hk heq) k) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  intro f hf
  obtain ⟨r⟩ := hard f hf
  exact ⟨r.controlledCompose (reduction L k hk heq)⟩

end
end Paper2.DegreeCSP.DisequalitySource
