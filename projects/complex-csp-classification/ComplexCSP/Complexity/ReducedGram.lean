import ComplexCSP.Complexity.CSPColorRelabeling
import ComplexCSP.Instances.ValueTransport
import ComplexCSP.Algebra.GramObstruction
import ComplexCSP.Structure.PhaseSupportObstruction
import ComplexCSP.Complexity.CSPCoefficientTransport

/-! # The exact output interface of the non-BO obstruction reduction -/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityReducedGram
open scoped BigOperators
open PlanarHom PlanarHom.Complexity

/-- A single ordinary binary constraint, with arbitrary finite color type. -/
def binaryLanguage {R K : Type} (A : R → R → K) : Language R K (Fin 1) :=
  ⟨fun _ => 2,fun _ => Nat.zero_lt_succ 1,fun _ a => A (a 0) (a 1)⟩

def StrictPrincipalMinor {R : Type} (A : R → R → ℂ) : Prop :=
  ∃ x y,0<‖A x x‖ ∧ 0<‖A x y‖ ∧ 0<‖A y y‖ ∧
    ‖A x y‖*‖A y x‖ < ‖A x x‖*‖A y y‖

/-- Constructed output data, not an assumed dichotomy or hardness certificate.
Both finite matrix dimensions and the actual bit-costed oracle reduction are
present. The common field interprets the original language literally. -/
structure Witness {D : Type} [Fintype D] {s : ℕ} (L : Language D ℂ (Fin s)) where
  field : IntermediateField ℚ ℂ
  fieldFinite : FiniteDimensional ℚ field
  dimension : ℕ
  basis : Module.Basis (Fin dimension) ℚ field
  input : Language D field (Fin s)
  input_correct : input.mapValues field.subtype = L
  colors : ℕ
  columns : ℕ
  matrix : Fin colors → Fin colors → field
  factor : Fin colors → Fin columns → ℝ
  factor_nonneg : ∀ i z,0≤factor i z
  gram : ∀ i j,(matrix i j : ℂ) = ((∑ z,factor i z*factor j z : ℝ) : ℂ)
  obstruction : StrictPrincipalMinor (fun i j => (matrix i j : ℂ))
  reduction : PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem (binaryLanguage matrix) basis)
    (ComplexityCSPCountReduction.partitionProblem input basis)

/-- Canonical finite reindexing costs no hidden oracle: it uses the proved
same-word color-relabeling machine and exact finite-sum transport. -/
def ofFinite {D R C : Type} [Fintype D] [Fintype R] [Fintype C] {s d : ℕ}
    (L : Language D ℂ (Fin s)) (K : IntermediateField ℚ ℂ) (hK : FiniteDimensional ℚ K)
    (basis : Module.Basis (Fin d) ℚ K) (input : Language D K (Fin s))
    (hinput : input.mapValues K.subtype=L) (A : R → R → K) (B : R → C → ℝ)
    (hB : ∀ i z,0≤B i z) (hGram : ∀ i j,(A i j : ℂ)=((∑ z,B i z*B j z : ℝ) : ℂ))
    (hminor : StrictPrincipalMinor (fun i j => (A i j : ℂ)))
    (hred : PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem (binaryLanguage A) basis)
      (ComplexityCSPCountReduction.partitionProblem input basis)) : Witness L := by
  let e := (Fintype.equivFin R).symm
  let f := (Fintype.equivFin C).symm
  refine ⟨K,hK,d,basis,input,hinput,Fintype.card R,Fintype.card C,
    (fun i j => A (e i) (e j)),(fun i z => B (e i) (f z)),(fun i z => hB _ _),?_,?_,?_⟩
  · intro i j
    rw [hGram]
    exact congrArg Complex.ofReal (f.sum_comp (fun z => B (e i) z*B (e j) z)).symm
  · obtain ⟨x,y,hxx,hxy,hyy,hdet⟩ := hminor
    refine ⟨e.symm x,e.symm y,?_⟩
    simpa only [Equiv.apply_symm_apply] using And.intro hxx (And.intro hxy (And.intro hyy hdet))
  · exact (ComplexityCSPColorRelabeling.reduction (binaryLanguage A) e basis).trans hred

/-- The finite strict-minor theorem is transported through actual Gram entry
identities, without assuming a hardness theorem or a principal-submatrix oracle. -/
theorem strict_minor_of_norm_gram {R C : Type} [Fintype C]
    {K : IntermediateField ℚ ℂ} (G : R → C → ℂ)
    (hbad : ¬BlockOrthogonality.BlockRankOne G) (A : R → R → K)
    (hA : ∀ i j,(A i j : ℂ)=((∑ z,‖G i z‖*‖G j z‖ : ℝ) : ℂ)) :
    StrictPrincipalMinor (fun i j => (A i j : ℂ)) := by
  have hn (i j : R) : ‖(A i j : ℂ)‖=GramObstruction.gram (fun i z => ‖G i z‖) i j := by
    rw [hA]
    simp only [Complex.norm_real,Real.norm_eq_abs]
    exact abs_of_nonneg (GramObstruction.gram_nonneg _ (fun _ _ => norm_nonneg _) i j)
  obtain ⟨i,j,hii,hij,hjj,hdet⟩ := GramObstruction.complex_obstruction G hbad
  exact ⟨i,j,by simpa only [hn] using And.intro hii (And.intro hij (And.intro hjj hdet))⟩

namespace Witness
variable {D : Type} [Fintype D] {s : ℕ} {L : Language D ℂ (Fin s)} (W : Witness L)

theorem symmetric (i j : Fin W.colors) : W.matrix i j=W.matrix j i := by
  apply Subtype.ext
  rw [W.gram,W.gram]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  exact mul_comm _ _

theorem real_entries (i j : Fin W.colors) : (W.matrix i j : ℂ).im=0 := by rw [W.gram]; rfl

theorem nonnegative_entries (i j : Fin W.colors) : 0≤(W.matrix i j : ℂ).re := by
  rw [W.gram]
  simpa only [Complex.ofReal_re] using
    (Finset.sum_nonneg (s:=Finset.univ) (fun z _ => mul_nonneg (W.factor_nonneg i z) (W.factor_nonneg j z)))

theorem not_blockRankOne : ¬BlockOrthogonality.BlockRankOne (fun i j => (W.matrix i j : ℂ)) := by
  obtain ⟨i,j,hii,hij,hjj,hdet⟩ := W.obstruction
  exact PhaseSupportObstruction.not_blockRankOne_of_minor _ i j hii hij hjj hdet

theorem colors_ge_two : 2≤W.colors := by
  obtain ⟨i,j,hii,hij,hjj,hdet⟩ := W.obstruction
  by_contra h
  have he : i=j := Fin.ext (by have := i.isLt; have := j.isLt; omega)
  subst j
  exact (lt_irrefl _ hdet)

/-- The exact input oracle values are literally the user's original complex
partition values after applying the constructed coefficient embedding. -/
theorem input_partition (g : ComplexityCSPCode.Code) :
    ((ComplexityCSPCode.partition W.input g : W.field) : ℂ)=ComplexityCSPCode.partition L g := by
  conv_rhs => rw [←W.input_correct]
  exact (ComplexityCSPCoefficientTransport.partition_mapValues W.input W.field.subtype g).symm

end Witness
end ComplexCSP.ComplexityReducedGram
