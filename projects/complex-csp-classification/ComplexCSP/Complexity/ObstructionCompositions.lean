import ComplexCSP.Complexity.GramReduction
import ComplexCSP.Complexity.GadgetSubstitutionReduction
import ComplexCSP.Complexity.CSPReplacement

/-! # Composing the actual obstruction machines inside one common field -/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityObstructionCompositions
open PlanarHom PlanarHom.Complexity ComplexityCSPCode ComplexityCSPCountReduction
variable {D K : Type} [Fintype D] [Field K] [DecidableEq K] [Algebra ℚ K]
variable {s r dimension : ℕ} (L : Language D K (Fin s))
variable (basis : Module.Basis (Fin dimension) ℚ K)

def presentationReduction (P : Presentation L (Fin (r+1))) :
    PromisePolyTimeTuringReduction (partitionProblem (GramGadget.language P.table) basis)
      (partitionProblem L basis) :=
  ComplexityGadgetSubstitution.unrestrictedReduction basis (fun _ => P) (fun _ _ => rfl)

/-- Replace the actual generated table by a multiplicatively consistent table,
then expand every original generated constraint using its literal presentation. -/
def purifiedPresentationReduction (P : Presentation L (Fin (r+1)))
    (Q : (Fin (r+1) → D) → K)
    (hc : ProductCompatibility.Compatible (entryValue (GramGadget.language P.table))
      (ComplexityCSPReplacement.targetEntry (GramGadget.language P.table) (fun _ => Q)))
    (hz : ∀ a,P.table a=0 → Q a=0) :
    PromisePolyTimeTuringReduction (partitionProblem (GramGadget.language Q) basis)
      (partitionProblem L basis) := by
  have hc' := hc.comp (Fintype.equivFin (Entry (GramGadget.language P.table))).symm
  have hz' : ∀ i,ComplexityCSPNodes.alphabet (GramGadget.language P.table) i=0 →
      ComplexityCSPReplacement.targetAlphabet (GramGadget.language P.table) (fun _ => Q) i=0 := by
    intro i hi
    unfold ComplexityCSPNodes.alphabet at hi
    unfold ComplexityCSPReplacement.targetAlphabet
    cases he : (Fintype.equivFin (Entry (GramGadget.language P.table))).symm i with
    | none => simp [he,entryValue] at hi
    | some ia =>
      simp only [he,entryValue] at hi
      change P.table ia.2 = 0 at hi
      exact hz ia.2 hi
  let rep := ComplexityCSPReplacement.reduction (GramGadget.language P.table) (fun _ => Q) basis hc' hz'
  exact rep.trans (presentationReduction L basis P)

variable {L}

/-- Nonnegative Gram evaluation is reduced to the original table by one fixed
edge gadget followed by the exact absolute-value replacement machine. -/
def absoluteGramReduction (F A : (Fin (r+1) → D) → K) (hr : 0<r)
    (σ : K →+* ℂ) (hA : ∀ a,σ (A a)=(‖σ (F a)‖ : ℂ)) :
    PromisePolyTimeTuringReduction
      (partitionProblem (ComplexityGramReduction.sourceLanguage A 1 1) basis)
      (partitionProblem (GramGadget.language F) basis) :=
  (ComplexityGramReduction.reduction A 1 1 hr basis).trans
    (ComplexityCSPReplacement.absoluteReduction (GramGadget.language F) (fun _ => A)
      basis σ (fun _ a => hA a))

/-- The phase branch's extra Gram and two-power query are composed, including
all tuple-variable expansion and exact-field recovery costs. -/
def phaseGramReduction (F : (Fin (r+1) → D) → K) (p q : ℕ) (hr : 0<r)
    (A : (Fin 2 → (Fin r → D)) → K) (σ : K →+* ℂ)
    (hA : ∀ a,σ (A a)=(‖σ (GramPowerGadget.matrix F p q (a 0) (a 1))‖ : ℂ)) :
    PromisePolyTimeTuringReduction
      (partitionProblem (ComplexityGramReduction.sourceLanguage A 1 1) basis)
      (partitionProblem (GramGadget.language F) basis) :=
  (absoluteGramReduction basis (fun a => GramPowerGadget.matrix F p q (a 0) (a 1))
    A (by decide) σ hA).trans (ComplexityGramReduction.reduction F p q hr basis)

end ComplexCSP.ComplexityObstructionCompositions
