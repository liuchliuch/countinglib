import ComplexCSP.Algebra.FiniteValueField
import ComplexCSP.Algebra.LegalSingletonPurification
import ComplexCSP.Complexity.ObstructionCompositions

set_option backward.isDefEq.respectTransparency false

/-! # Interpreting the selected obstruction witness in one constructed field -/
noncomputable section
open Classical
namespace ComplexCSP.ObstructionCommonRepresentation
open PlanarHom PlanarHom.Complexity ComplexityCSPCode FiniteValueField
variable {D E : Type} [Fintype D] [Fintype E] {s : ℕ}
variable (L : Language D ℂ (Fin s)) (extra : E → ℂ)
variable (hL : ∀ i a,IsAlgebraic ℚ (L.value i a)) (he : ∀ e,IsAlgebraic ℚ (extra e))
variable (T : PositiveTable D) (P : Presentation L (Fin (T.rowArity+1))) (hP : P.table=T.value)
variable (hQ : ∀ a,LegalSingletonPurification.value T a ∈ inputField L extra)

def purified (a : Fin (T.rowArity+1) → D) : inputField L extra :=
  ⟨LegalSingletonPurification.value T a,hQ a⟩

include hP in
theorem original_coe (a : Fin (T.rowArity+1) → D) :
    ((inputPresentation L extra P).table a : ℂ)=T.value a := by
  rw [table_inputPresentation,hP]

/-- All multiplication tests are transferred from the proved legal map into
this exact common coordinate field; the actual presentation supplies the final
query to the input language. -/
def reduction : PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem (GramGadget.language (purified L extra T hQ))
      (inputBasis L extra hL he))
    (ComplexityCSPCountReduction.partitionProblem (inputLanguage L extra) (inputBasis L extra hL he)) := by
  let σ := (inputField L extra).subtype
  let P0 := inputPresentation L extra P
  let Q0 := purified L extra T hQ
  have hc : ProductCompatibility.Compatible
      (entryValue (GramGadget.language P0.table))
      (ComplexityCSPReplacement.targetEntry (GramGadget.language P0.table) (fun _ => Q0)) := by
    apply ComplexityReplacementField.compatible_of_embedding σ
    convert LegalSingletonPurification.entries_compatible T using 1
    · rfl
    · funext a
      cases a with
      | none => rfl
      | some ia => exact original_coe L extra T P hP ia.2
    · funext a
      cases a <;> rfl
  have hz : ∀ a,P0.table a=0 → Q0 a=0 := by
    intro a ha
    apply Subtype.ext
    apply LegalSingletonPurification.zero T a
    rw [←original_coe L extra T P hP a]
    change σ (P0.table a)=0
    rw [ha,map_zero]
  exact ComplexityObstructionCompositions.purifiedPresentationReduction
    (inputLanguage L extra) (inputBasis L extra hL he) P0 Q0 hc hz

end ComplexCSP.ObstructionCommonRepresentation
