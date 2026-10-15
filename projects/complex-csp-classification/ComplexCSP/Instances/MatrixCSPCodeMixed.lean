import ComplexCSP.Instances.MatrixCSPMixedAdapter
import ComplexCSP.Instances.RootedCSPMachines

/-! # Lossless canonical binary CSP to mixed occurrence code conversion -/
namespace ComplexCSP.MatrixCSPCodeMixed
open PlanarHom PlanarHom.Complexity PairProjectionMachines
open ComplexityCSPCode

def edge (c : ℕ × List ℕ) : MatrixCSPMixedAdapter.Edge := (c.2.getD 0 0,c.2.getD 1 0,0)
def toMixed (g : Code) : MixedCode := ⟨g.vertices,g.constraints.map edge,[]⟩

variable {D K : Type} (A : D → D → K)

theorem valid_row (n : ℕ) (c : ℕ × List ℕ)
    (hc : ConstraintValid (MatrixCSP.language A) n c) :
    c.1=0 ∧ ∃ u v,c.2=[u,v] ∧ u<n ∧ v<n := by
  obtain ⟨hs,hl,hv⟩ := hc
  have hs0 : c.1=0 := by omega
  obtain ⟨u,v,he⟩ := List.length_eq_two.mp hl
  exact ⟨hs0,u,v,he,hv u (by simp [he]),hv v (by simp [he])⟩

theorem valid (g : Code) (hg : Valid (MatrixCSP.language A) g) : (toMixed g).Valid 1 0 := by
  constructor
  · intro e he
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp he
    obtain ⟨_,u,v,he,hu,hv⟩ := valid_row A g.vertices c (hg c hc)
    simpa [toMixed,edge,he] using And.intro hu (And.intro hv Nat.zero_lt_one)
  · intro u hu
    simp [toMixed] at hu

theorem toCode_toMixed (g : Code) (hg : Valid (MatrixCSP.language A) g) :
    MatrixCSPMixedAdapter.toCode (toMixed g) = g := by
  unfold MatrixCSPMixedAdapter.toCode toMixed
  cases g with
  | mk n cs =>
    apply congrArg (Code.mk n)
    rw [List.map_map]
    change cs.map _ = cs
    conv_rhs => rw [← List.map_id cs]
    apply List.map_congr_left
    intro c hc
    obtain ⟨hs,u,v,he,_,_⟩ := valid_row A n c (hg c hc)
    apply Prod.ext
    · exact hs.symm
    · simp [edge,MatrixCSPMixedAdapter.edgeConstraint,he]

theorem toMixed_toCode (g : MixedCode) (hg : g.Valid 1 0) :
    toMixed (MatrixCSPMixedAdapter.toCode g) = g := by
  have hu := MatrixCSPMixedAdapter.unaries_nil g hg
  have he : (g.edges.map MatrixCSPMixedAdapter.edgeConstraint).map edge = g.edges := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id g.edges]
    apply List.map_congr_left
    intro e he
    have hl : e.2.2=0 := by have := (hg.1 e he).2.2; omega
    simp only [Function.comp_apply,edge,MatrixCSPMixedAdapter.edgeConstraint]
    simp only [List.getD_cons_zero,List.getD_cons_succ]
    exact Prod.ext rfl (Prod.ext rfl hl.symm)
  cases g with
  | mk n es us =>
    change (⟨n,(es.map MatrixCSPMixedAdapter.edgeConstraint).map edge,[]⟩ : MixedCode) = ⟨n,es,us⟩
    change (es.map MatrixCSPMixedAdapter.edgeConstraint).map edge = es at he
    change us = [] at hu
    rw [he,hu]

theorem fp_edge : FP constraintEncoding
    (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)) edge := by
  have hs := fp_snd BitEncoding.nat BitEncoding.nat.list
  exact (hs.comp (RootedCSPProjection.fp_getD BitEncoding.nat 0 0)).pair
    ((hs.comp (RootedCSPProjection.fp_getD BitEncoding.nat 1 0)).pair
      (fp_const constraintEncoding BitEncoding.nat 0))

theorem fp_toMixed : FP encoding MixedCode.encoding toMixed := by
  have he := ComplexityGadgetSubstitution.fp_constraints.comp
    (ListMapMachines.fp_map constraintEncoding
      (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)) edge fp_edge)
  exact (ComplexityGadgetSubstitution.fp_vertices.pair
    (he.pair (fp_const encoding MixedCode.unaryEncoding []))).transportOutput (fun _ => rfl)

end ComplexCSP.MatrixCSPCodeMixed
