import PlanarHom.ColoredSignatureFieldMap
import PlanarHom.UnitBackgroundLanguage

/-! NEW literal colored gadget matrices in the canonical source field.
These are algebraicity and exact finite-sum facts only. No gadget availability
or source algorithm is inferred from an algebraic signature. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
variable {q bt ut : ℕ} {J E : Type} [Fintype J] [Fintype E]

def coloredGadgetMatrix (L : RealLanguage q bt ut) (G : TwoTerminal J E) (label : E→Fin bt) :
    Matrix (Fin q) (Fin q) ℝ :=
  TwoTerminal.coloredSignature G (fun e=>L.matrices (label e)) (fun _=>1)

def coloredGadgetMatrixK (L : RealLanguage q bt ut) (G : TwoTerminal J E) (label : E→Fin bt) :
    Matrix (Fin q) (Fin q) L.field :=
  TwoTerminal.coloredSignature G (fun e=>L.matricesK (label e)) (fun _=>1)

set_option backward.isDefEq.respectTransparency false in
theorem coloredGadgetMatrixK_coe (L : RealLanguage q bt ut) (G : TwoTerminal J E)
    (label : E→Fin bt) (i j : Fin q) :
    (coloredGadgetMatrixK L G label i j:ℝ)=coloredGadgetMatrix L G label i j := by
  have hM : (fun e a b => L.field.val.toRingHom (L.matricesK (label e) a b)) =
      (fun e => L.matrices (label e)) := rfl
  have h := TwoTerminal.map_coloredSignature L.field.val.toRingHom G
    (fun e=>L.matricesK (label e)) (fun _=>1) i j
  rw [hM] at h
  simpa only [coloredGadgetMatrixK,coloredGadgetMatrix,map_one,
    AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,IntermediateField.coe_val] using h

theorem coloredGadgetMatrix_algebraic (L : RealLanguage q bt ut) (G : TwoTerminal J E)
    (label : E→Fin bt) (i j : Fin q) : IsAlgebraic ℚ (coloredGadgetMatrix L G label i j) := by
  rw [←coloredGadgetMatrixK_coe L G label i j]
  exact (IsAlgebraic.of_finite ℚ (coloredGadgetMatrixK L G label i j)).algHom L.field.val

/-- The exact two-occurrence product used by the recovered parallel closure. -/
theorem colored_parallel_pair (H K : Matrix (Fin q) (Fin q) ℝ) :
    TwoTerminal.coloredSignature (TwoTerminal.parallelEdges 2)
      (Fin.cases H (fun _=>K)) (fun _=>1) = fun i j=>H i j*K i j := by
  funext i j
  simp [TwoTerminal.coloredSignature,TwoTerminal.parallelEdges,TwoTerminal.extend,Fin.prod_univ_succ]

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
