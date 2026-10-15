import ComplexCSP.Algebra.PositiveBinaryApex
import ComplexCSP.Complexity.GadgetSubstitutionSemantics

/-! # One shared root realizes an arbitrary-color conditioned matrix

Every input edge occurrence is replaced by its triangle with the same root.
The original vertices, including isolates, remain distinct hidden variables.
-/
namespace ComplexCSP.ConditionedMatrixCode
open ComplexityCSPCode ComplexityGadgetSubstitution
open scoped BigOperators

variable {D K : Type} [CommSemiring K]

def conditioned (A : D → D → K) (z : D) (i j : D) : K := A i j * A i z * A j z

/-- Raw total syntax operation; even malformed rows have a defined output. -/
def edgeTriangles (c : ℕ × List ℕ) : List (ℕ × List ℕ) :=
  let u := c.2.getD 0 0 + 1
  let v := c.2.getD 1 0 + 1
  [(0,[u,v]),(0,[u,0]),(0,[v,0])]

def rootCode (g : Code) : Code :=
  ⟨1+g.vertices,g.constraints.flatMap edgeTriangles⟩

def rootConstraints (A B : D → D → K) {n : ℕ}
    (c : Constraint (MatrixCSP.language B) (Fin n)) :
    List (Constraint (MatrixCSP.language A) (Fin 1 ⊕ Fin n)) :=
  let u := Sum.inr (c.scope (0 : Fin 2))
  let v := Sum.inr (c.scope (1 : Fin 2))
  let z := Sum.inl (0 : Fin 1)
  [⟨0,![u,v]⟩,⟨0,![u,z]⟩,⟨0,![v,z]⟩]

def rootedPresentation (A B : D → D → K) (g : Code)
    (hg : Valid (MatrixCSP.language B) g) : Presentation (MatrixCSP.language A) (Fin 1) :=
  ⟨g.vertices,⟨(decodedGates (MatrixCSP.language B) g hg).flatMap (rootConstraints A B)⟩⟩

omit [CommSemiring K] in
theorem rootConstraints_codes (A B : D → D → K) {n : ℕ}
    (c : Constraint (MatrixCSP.language B) (Fin n)) :
    ((rootConstraints A B c).map constraintCode) = edgeTriangles (gateCode c) := by
  simp [rootConstraints,constraintCode,edgeTriangles,gateCode,MatrixCSP.language,
    List.ofFn_succ,Nat.add_comm]

omit [CommSemiring K] in
theorem rootedPresentation_code (A B : D → D → K) (g : Code)
    (hg : Valid (MatrixCSP.language B) g) :
    presentationCode (rootedPresentation A B g hg) = rootCode g := by
  unfold presentationCode presentationTemplate Template.code rootedPresentation rootCode
  congr 1
  rw [List.map_flatMap]
  simp only [rootConstraints_codes]
  rw [← List.flatMap_map,gateCode_decodedGates]

variable [Fintype D]

omit [Fintype D] in
theorem rootConstraints_eval (A B : D → D → K) {n : ℕ}
    (c : Constraint (MatrixCSP.language B) (Fin n)) (a : Fin 1 → D) (σ : Fin n → D) :
    ((rootConstraints A B c).map (fun d => d.eval (Sum.elim a σ))).prod =
      conditioned A (a 0) (σ (c.scope (0 : Fin 2))) (σ (c.scope (1 : Fin 2))) := by
  simp [rootConstraints,Constraint.eval,MatrixCSP.language,conditioned,mul_assoc]

omit [Fintype D] in
theorem rootedPresentation_eval (A B : D → D → K) (g : Code)
    (hg : Valid (MatrixCSP.language B) g) (a : Fin 1 → D) (σ : Fin g.vertices → D) :
    (rootedPresentation A B g hg).inst.eval a σ =
      ((decodedGates (MatrixCSP.language B) g hg).map (fun c =>
        conditioned A (a 0) (σ (c.scope (0 : Fin 2))) (σ (c.scope (1 : Fin 2))))).prod := by
  simp only [rootedPresentation,Instance.eval,List.flatMap_def,List.map_flatten,List.prod_flatten,List.map_map,
    Function.comp_def,rootConstraints_eval]

set_option backward.isDefEq.respectTransparency false in
theorem rootedPresentation_table (A : D → D → K) (z : D) (g : Code)
    (hg : Valid (MatrixCSP.language (conditioned A z)) g) :
    (rootedPresentation A (conditioned A z) g hg).table (fun _ => z) =
      partition (MatrixCSP.language (conditioned A z)) g := by
  unfold Presentation.table Instance.partition partition
  apply Finset.sum_congr rfl
  intro σ _
  rw [rootedPresentation_eval]
  exact decodedGates_product (MatrixCSP.language (conditioned A z)) g hg σ

omit [Fintype D] [CommSemiring K] in
theorem rootCode_valid (A B : D → D → K) (g : Code)
    (hg : Valid (MatrixCSP.language B) g) : Valid (MatrixCSP.language A) (rootCode g) := by
  rw [← rootedPresentation_code A B g hg]
  exact presentationCode_valid _

end ComplexCSP.ConditionedMatrixCode
