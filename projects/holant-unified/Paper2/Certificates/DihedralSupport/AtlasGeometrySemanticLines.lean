import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticLinear
import Paper2.Certificates.DihedralSupport.AtlasCountsIncidence

/-! Rich projective lines are actual two-dimensional subspaces. The finite
image below exhausts every such subspace containing three atlas points. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic
open AtlasGeometry AtlasCounts
noncomputable section
variable {K I : Type*} [Field K]

def richLineSpace (V : PointLabel→I→K) (r : RichLabel) : Submodule K (I→K) :=
  Submodule.span K ({V (richPoints r 0),V (richPoints r 1)} : Set (I→K))

def richLines (V : PointLabel→I→K) : Finset (Submodule K (I→K)) := by
  classical
  exact Finset.univ.image (richLineSpace V)

def RichLine (V : PointLabel→I→K) (L : Submodule K (I→K)) : Prop :=
  Module.finrank K L=2 ∧ ∃ p q t : PointLabel,
    p≠q ∧ p≠t ∧ q≠t ∧ V p∈L ∧ V q∈L ∧ V t∈L

def linePoints (V : PointLabel→I→K) (L : Submodule K (I→K)) : Finset PointLabel := by
  classical
  exact Finset.univ.filter (fun l => V l∈L)

private theorem rich_points_01_ne (r : RichLabel) : richPoints r 0≠richPoints r 1 := by
  intro hh
  have := richPoints_distinct r hh
  norm_num at this

private theorem rich_point_mem (r : RichLabel) (j : Fin 3) : richPoints r j∈richSet r :=
  Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩

theorem richLineSpace_finrank (V : PointLabel→I→K)
    (hpair : ∀ p q, p≠q → ∃ a b, minor2 (V p) (V q) a b≠0)
    (r : RichLabel) : Module.finrank K (richLineSpace V r)=2 := by
  obtain ⟨a,b,hab⟩ := hpair _ _ (rich_points_01_ne r)
  exact span_pair_finrank hab

theorem richLineSpace_injective (V : PointLabel→I→K)
    (hinc : ∀ r l, V l∈richLineSpace V r ↔ l∈richSet r) :
    Function.Injective (richLineSpace V) := by
  intro r s hrs
  apply richSet_injective
  ext l
  rw [←hinc r l,←hinc s l,hrs]

theorem richLines_card (V : PointLabel→I→K)
    (hinc : ∀ r l, V l∈richLineSpace V r ↔ l∈richSet r) :
    (richLines V).card=202 := by
  classical
  rw [richLines,Finset.card_image_of_injective _ (richLineSpace_injective V hinc)]
  simpa using rich_card

theorem richLineSpace_rich (V : PointLabel→I→K)
    (hpair : ∀ p q, p≠q → ∃ a b, minor2 (V p) (V q) a b≠0)
    (hinc : ∀ r l, V l∈richLineSpace V r ↔ l∈richSet r)
    (r : RichLabel) : RichLine V (richLineSpace V r) := by
  refine ⟨richLineSpace_finrank V hpair r,richPoints r 0,richPoints r 1,
    richPoints r 2,rich_points_01_ne r,?_,?_,?_,?_,?_⟩
  · intro hh; have := richPoints_distinct r hh; norm_num at this
  · intro hh; have := richPoints_distinct r hh; norm_num at this
  · exact (hinc r _).mpr (rich_point_mem r 0)
  · exact (hinc r _).mpr (rich_point_mem r 1)
  · exact (hinc r _).mpr (rich_point_mem r 2)

theorem richLines_complete (V : PointLabel→I→K)
    (hpair : ∀ p q, p≠q → ∃ a b, minor2 (V p) (V q) a b≠0)
    (hclass : ∀ p q t, p≠q → p≠t → q≠t → OnLine (V p) (V q) (V t) →
      ∃ r, richSet r={p,q,t})
    (L : Submodule K (I→K)) (hL : RichLine V L) :
    ∃ r, L=richLineSpace V r := by
  classical
  obtain ⟨hdim,p,q,t,hpq,hpt,hqt,hp,hq,ht⟩ := hL
  obtain ⟨a,b,hab⟩ := hpair p q hpq
  have heq := two_dimensional_line_eq_span hab L hdim hp hq
  have hline : OnLine (V p) (V q) (V t) := by
    apply (onLine_iff_mem_span _ _ _).mpr
    rw [←heq]
    exact ht
  obtain ⟨r,hr⟩ := hclass p q t hpq hpt hqt hline
  have hmem : ∀ l∈richSet r, V l∈L := by
    intro l hl
    rw [hr] at hl
    simp only [Finset.mem_insert,Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact ht
  have hle : richLineSpace V r≤L := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | hx
    · exact hmem _ (rich_point_mem r 0)
    · have he : x=V (richPoints r 1) := Set.mem_singleton_iff.mp hx
      exact he ▸ hmem _ (rich_point_mem r 1)
  let : Module.Finite K L := Module.finite_of_finrank_eq_succ hdim
  exact ⟨r,(Submodule.eq_of_le_of_finrank_eq hle
    ((richLineSpace_finrank V hpair r).trans hdim.symm)).symm⟩

theorem mem_richLines_iff (V : PointLabel→I→K)
    (hpair : ∀ p q, p≠q → ∃ a b, minor2 (V p) (V q) a b≠0)
    (hinc : ∀ r l, V l∈richLineSpace V r ↔ l∈richSet r)
    (hclass : ∀ p q t, p≠q → p≠t → q≠t → OnLine (V p) (V q) (V t) →
      ∃ r, richSet r={p,q,t})
    (L : Submodule K (I→K)) : L∈richLines V ↔ RichLine V L := by
  classical
  constructor
  · intro h
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp h
    exact richLineSpace_rich V hpair hinc r
  · intro h
    obtain ⟨r,rfl⟩ := richLines_complete V hpair hclass L h
    exact Finset.mem_image.mpr ⟨r,Finset.mem_univ _,rfl⟩

theorem rich_line_point_count (V : PointLabel→I→K)
    (hinc : ∀ r l, V l∈richLineSpace V r ↔ l∈richSet r) (r : RichLabel) :
    (linePoints V (richLineSpace V r)).card=3 := by
  classical
  have heq : Finset.univ.filter (fun l => V l∈richLineSpace V r)=richSet r := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,hinc]
  rw [linePoints,heq]
  exact richSet_card r

end
end Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic

