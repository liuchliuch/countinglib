import ComplexCSP.Instances.MatrixCSPMixedAdapter
import ComplexCSP.Instances.RootedCSPCodePresentation
import PlanarHom.RootedColorRestriction

set_option backward.isDefEq.respectTransparency false

/-! # Support-closed color restriction on a connected general input

This invokes no planar promise and no restriction to an arbitrary principal
submatrix. The color subset must be closed under actual nonzero matrix entries.
-/
noncomputable section
open Classical
namespace ComplexCSP.SupportComponentSemantics
open PlanarHom PlanarHom.Complexity
open ComplexityCSPCode MatrixCSPMixedAdapter RootedCSPCodePresentation
open scoped BigOperators
variable {D K : Type} [Fintype D] [Field K]

/-- Literal root-subset weight; it retains every color in the subset. -/
def subsetWeight (X : Set D) (a : Fin 1 → D) : K := by
  classical
  exact if a 0 ∈ X then 1 else 0

theorem eval_toCode_assignmentWeight (A : D → D → K) (g : MixedCode) (hg : g.Valid 1 0)
    (σ : Fin g.vertices → D) :
    eval (MatrixCSP.language A) (toCode g) σ =
      (g.toMultiGraph hg).assignmentWeight A (fun _ => 1) σ := by
  unfold eval assignmentWord toCode
  simp only [List.map_map,Function.comp_def]
  calc
    _ = (g.edges.map (MixedCode.binaryValue g.vertices 1 (fun _ : Fin 1 => A) σ)).prod := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro e he
      exact constraint_value A g e (hg.1 e he) σ
    _ = _ := by
      unfold MultiGraph.assignmentWeight
      simp only [Finset.prod_const_one,one_mul]
      rw [← Fin.prod_univ_fun_getElem]
      apply Finset.prod_congr rfl
      intro e _
      have hv := hg.1 (g.edges.get e) (List.get_mem _ _)
      simp only [List.get_eq_getElem] at hv
      simp only [MixedCode.binaryValue,dif_pos hv,MixedCode.toMultiGraph,List.get_eq_getElem]

theorem rootSum_toCode (A : D → D → K) (X : Set D) (g : MixedCode)
    (hg : g.Valid 1 0) (hn : 0 < g.vertices) :
    rootSum (MatrixCSP.language A) (subsetWeight X) (toCode g) =
      (g.toMultiGraph hg).rootRestricted ⟨0,hn⟩ A (fun _ => 1) X := by
  classical
  rw [rootSum,dif_pos (show 0 < (toCode g).vertices from hn)]
  unfold MultiGraph.rootRestricted
  apply Finset.sum_congr
  · ext σ; simp
  intro σ _
  rw [eval_toCode_assignmentWeight A g hg]
  simp [subsetWeight]

/-- The actual submatrix value follows from one root sum only because the input
is connected and the color set is support closed. -/
theorem connected_submatrix (A : D → D → K) (hs : ∀ i j,A i j=A j i)
    (X : Set D) (hX : RootedRestriction.ColorClosed A X)
    (g : MixedCode) (hg : g.Valid 1 0) (hc : (GraphComponentCode.support g).Connected)
    (hn : 0 < g.vertices) :
    rootSum (MatrixCSP.language A) (subsetWeight X) (toCode g) =
      partition (MatrixCSP.language (fun i j : X => A i.val j.val)) (toCode g) := by
  classical
  rw [rootSum_toCode A X g hg hn,
    RootedRestriction.rootRestricted_eq_submatrix g hg hc ⟨0,hn⟩ A hs (fun _ => 1) X hX,
    partition_toCode _ g hg,MixedCode.evaluate_homogeneous]

end ComplexCSP.SupportComponentSemantics
