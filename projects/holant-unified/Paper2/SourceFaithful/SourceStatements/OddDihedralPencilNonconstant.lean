import Paper2.SourceFaithful.SourceStatements.OddDihedralPencilStatement
import Paper2.Certificates.DihedralSupport.AtlasParityFrameGeometry

/-! A projectively nonconstant pencil has three distinct nonzero atlas
points. The claims use actual field minors and retain every phase scalar. -/
namespace Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
open Paper2.HeightOne Paper2.HeightOne.Dihedral SixPortSupport SixPortPencils
open Paper2.Certificates.DihedralSupport AtlasCounts AtlasGeometry
noncomputable section
set_option maxRecDepth 4096

variable {K : Type} [Field K]

/-- The two actual source slices span a two-dimensional space. This is the
coefficient criterion for projective nonconstancy of the phase pencil. -/
def NonconstantPencil (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (xi : Bool) : Prop :=
  ∃ x y : Word4, minor2 (first f p xi) (second f p xi) x y ≠ 0

theorem pencil_minor (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (s t : K) (x y : Word4) :
    minor2 (pencil f p xi s) (pencil f p xi t) x y =
      (s-t) * minor2 (first f p xi) (second f p xi) x y := by
  dsimp [minor2,pencil]
  ring

theorem phase_pair_independent (omega : K) (h : IsPrimitiveRoot omega 3)
    (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (hn : NonconstantPencil f p xi) (i j : Fin 3) (hij : i ≠ j) :
    ∃ x y, minor2 (pencil f p xi (omega ^ i.val)) (pencil f p xi (omega ^ j.val)) x y ≠ 0 := by
  obtain ⟨x,y,hxy⟩ := hn
  refine ⟨x,y,?_⟩
  rw [pencil_minor]
  exact mul_ne_zero (sub_ne_zero.mpr ((phase_injective omega h).ne hij)) hxy

theorem phase_cards_nonzero (omega : K) (h : IsPrimitiveRoot omega 3)
    (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (hn : NonconstantPencil f p xi) (i : Fin 3) :
    pencil f p xi (omega ^ i.val) ≠ 0 := by
  have hk : ∃ j : Fin 3, i ≠ j := by fin_cases i <;> decide +kernel
  obtain ⟨j,hij⟩ := hk
  obtain ⟨x,y,hxy⟩ := phase_pair_independent omega h f p xi hn i j hij
  exact nonzero_left_of_minor2 hxy

theorem pencil_minor3_zero (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (s t u : K) (x y z : Word4) :
    minor3 (pencil f p xi s) (pencil f p xi t) (pencil f p xi u) x y z = 0 := by
  dsimp [minor3,pencil]
  ring

theorem minor3_smul (a b c : K) (u v w : Word4 → K) (x y z : Word4) :
    minor3 (a • u) (b • v) (c • w) x y z = a*b*c * minor3 u v w x y z := by
  simp only [minor3,Pi.smul_apply,smul_eq_mul]
  ring

theorem labels_and_coefficients (omega : K) (h : IsPrimitiveRoot omega 3)
    (eta : Bool) (f : Signature K 6) (hf : AtlasContractions omega eta f)
    (p : Equiv.Perm (Fin 6)) (xi : Bool) (hn : NonconstantPencil f p xi) :
    ∃ labels : Fin 3 → PointLabel, ∃ scalars : Fin 3 → K,
      Function.Injective labels ∧ (∀ j, scalars j ≠ 0) ∧
      (∀ j, pencil f p xi (omega ^ j.val) =
        scalars j • AtlasParityFrame.table omega (eta ^^ xi) (labels j)) := by
  have hex : ∀ j : Fin 3, ∃ l : PointLabel, ∃ c : K,
      c ≠ 0 ∧ pencil f p xi (omega ^ j.val) = c • AtlasParityFrame.table omega (eta ^^ xi) l := by
    intro j
    exact (hf p xi j).resolve_left (phase_cards_nonzero omega h f p xi hn j)
  choose labels scalars hs he using hex
  refine ⟨labels,scalars,?_,hs,he⟩
  intro i j hij
  by_contra hnij
  obtain ⟨x,y,hxy⟩ := phase_pair_independent omega h f p xi hn i j hnij
  apply hxy
  rw [he i,he j,hij]
  simp only [minor2,Pi.smul_apply,smul_eq_mul]
  ring

theorem labels_minor3_zero (omega : K) (eta : Bool) (f : Signature K 6)
    (p : Equiv.Perm (Fin 6)) (xi : Bool) (labels : Fin 3 → PointLabel)
    (scalars : Fin 3 → K) (hs : ∀ j, scalars j ≠ 0)
    (he : ∀ j, pencil f p xi (omega ^ j.val) =
      scalars j • AtlasParityFrame.table omega (eta ^^ xi) (labels j)) :
    ∀ x y z : Word4,
      minor3 (AtlasParityFrame.table omega (eta ^^ xi) (labels 0))
        (AtlasParityFrame.table omega (eta ^^ xi) (labels 1))
        (AtlasParityFrame.table omega (eta ^^ xi) (labels 2)) x y z = 0 := by
  intro x y z
  have hh := pencil_minor3_zero f p xi (omega ^ (0 : Fin 3).val)
    (omega ^ (1 : Fin 3).val) (omega ^ (2 : Fin 3).val) x y z
  rw [he 0,he 1,he 2,minor3_smul] at hh
  exact (mul_eq_zero.mp hh).resolve_left (mul_ne_zero (mul_ne_zero (hs 0) (hs 1)) (hs 2))

theorem rich_phase_assignment (labels : Fin 3 → PointLabel) (hl : Function.Injective labels)
    (line : RichLabel) (he : richSet line = {labels 0,labels 1,labels 2}) :
    ∃ sigma : Equiv.Perm (Fin 3), ∀ j, richPoints line (sigma j) = labels j := by
  classical
  have hex : ∀ j : Fin 3, ∃ i : Fin 3, richPoints line i = labels j := by
    intro j
    have hj : labels j ∈ richSet line := by
      rw [he]
      fin_cases j <;> simp
    obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp hj
    exact ⟨i,hij⟩
  choose sigma hs using hex
  have hinj : Function.Injective sigma := by
    intro i j hij
    apply hl
    exact (hs i).symm.trans ((congrArg (richPoints line) hij).trans (hs j))
  refine ⟨Equiv.ofBijective sigma (Finite.injective_iff_bijective.mp hinj),hs⟩

end
end Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion

