import Paper2.Certificates.DihedralSupport.AtlasParityFrame
import Paper2.Certificates.DihedralSupport.CyclotomicComplex

/-! Appendix A.1(ii) with the literal 66-point atlas, all ordered-port xor
sectors, and all six phase-to-point assignments. The forbidden lines are the
actual secant and triangle labels of Appendix A.1(i). -/
namespace Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
open Paper2.Tractable Paper2.HeightOne Paper2.HeightOne.Cyclic Paper2.HeightOne.Dihedral
open SixPortSupport SixPortPencils
open Paper2.Certificates.DihedralSupport
open AtlasCounts
noncomputable section
set_option maxRecDepth 4096
local instance {α : Type*} : DecidableEq α := Classical.decEq α
variable {K : Type} [Field K]

def phaseSet (omega : K) : Finset K :=
  Finset.univ.image (fun j : Fin 3 => omega ^ j.val)

theorem phase_injective (omega : K) (h : IsPrimitiveRoot omega 3) :
    Function.Injective (fun j : Fin 3 => omega ^ j.val) := by
  intro i j hij
  exact Fin.ext (h.pow_inj i.isLt j.isLt hij)

theorem phaseSet_card (omega : K) (h : IsPrimitiveRoot omega 3) :
    (phaseSet omega).card = 3 := by
  rw [phaseSet,Finset.card_image_of_injective _ (phase_injective omega h)]
  simp

theorem phase_mem (omega : K) (j : Fin 3) :
    omega ^ j.val ∈ phaseSet omega := Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩

theorem phaseSet_root (omega : K) (h : IsPrimitiveRoot omega 3) :
    ∀ s ∈ phaseSet omega, s ^ 3 = 1 := by
  intro s hs
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hs
  rw [← pow_mul,Nat.mul_comm j.val 3,pow_mul,h.pow_eq_one,one_pow]

def pencil (f : Signature K 6) (p : Equiv.Perm (Fin 6))
    (xi : Bool) (s : K) : Signature K 4 :=
  fun x => first f p xi x - s * second f p xi x

theorem pencil_support (f : Signature K 6) (p : Equiv.Perm (Fin 6))
    (xi : Bool) (s : K) :
    pencilSupport (first f p xi) (second f p xi) s = Paper2.HeightOne.Cyclic.support (pencil f p xi s) := by
  ext x
  simp only [mem_pencilSupport,Paper2.HeightOne.Cyclic.mem_support,pencil]

/-- Every actual xor contraction is zero or a nonzero scalar multiple of
one of the 66 specified atlas signatures in its residual parity sector. -/
def AtlasContractions (omega : K) (eta : Bool)
    (f : Signature K 6) : Prop :=
  ∀ p xi (j : Fin 3), AtlasParityFrame.Admissible omega (eta ^^ xi) (pencil f p xi (omega ^ j.val))

/-- The actual three phase cards are projectively equal to the three points
of a typed rich line, in the phase assignment `sigma`. -/
def RichPencil (omega : K) (eta : Bool)
    (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (line : RichLabel) (sigma : Equiv.Perm (Fin 3)) : Prop :=
  ∀ j, ∃ c : K, c ≠ 0 ∧ pencil f p xi (omega ^ j.val) =
    c • AtlasParityFrame.table omega (eta ^^ xi) (richPoints line (sigma j))

theorem atlas_card_invariants (omega : K) (h : IsPrimitiveRoot omega 3)
    (eta : Bool) (f : Signature K 6) (hf : AtlasContractions omega eta f) :
    (∀ p xi s, s ∈ phaseSet omega →
      (pencilSupport (first f p xi) (second f p xi) s).card ≤ 4) ∧
    (∀ p xi s, s ∈ phaseSet omega → ∀ r,
      (first f p xi (complement r) - s * second f p xi (complement r)) ^ 3 =
      (first f p xi r - s * second f p xi r) ^ 3) := by
  have homega : omega ≠ 0 := cube_root_nonzero omega h.pow_eq_one
  constructor
  · intro p xi s hs
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hs
    rw [pencil_support]
    exact AtlasParityFrame.admissible_support_bound omega homega _ _ (hf p xi j)
  · intro p xi s hs r
    obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hs
    exact AtlasParityFrame.admissible_complement_cube omega h.pow_eq_one _ _ (hf p xi j) r

theorem projective_support (omega : K) (eta : Bool)
    (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (j : Fin 3) (l : PointLabel) (c : K) (hc : c ≠ 0)
    (he : pencil f p xi (omega ^ j.val) = c • AtlasParityFrame.table omega (eta ^^ xi) l) :
    pencilSupport (first f p xi) (second f p xi) (omega ^ j.val) =
      Paper2.HeightOne.Cyclic.support (AtlasParityFrame.table omega (eta ^^ xi) l) := by
  rw [pencil_support,he,AtlasParityFrame.support_smul c hc]

theorem no_secant_rich_pencil [CharZero K] (omega : K) (h : IsPrimitiveRoot omega 3)
    (eta : Bool) (f : Signature K 6) (hpar : HasParity f)
    (hf : AtlasContractions omega eta f) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (l : SecantLabel) (sigma : Equiv.Perm (Fin 3)) :
    ¬ RichPencil omega eta f p xi (.inr (.inr (.inl l))) sigma := by
  intro hline
  rcases l with ⟨pair,r,t⟩
  let j : Fin 3 := sigma.symm 0
  let k : Fin 3 := sigma.symm 1
  obtain ⟨c,hc,he⟩ := hline j
  obtain ⟨d,hd,hde⟩ := hline k
  have he' : pencil f p xi (omega ^ j.val) =
      c • AtlasParityFrame.table omega (eta ^^ xi) (single pair.1.1 r) := by
    simpa [j,richPoints] using he
  have hde' : pencil f p xi (omega ^ k.val) =
      d • AtlasParityFrame.table omega (eta ^^ xi) (single pair.1.2 t) := by
    simpa [k,richPoints] using hde
  have homega : omega ≠ 0 := cube_root_nonzero omega h.pow_eq_one
  have hjk : j ≠ k := by
    intro h'
    have h'' := congrArg sigma h'
    simp [j,k] at h''
  have hphases := (phase_injective omega h).ne hjk
  have hsupport := projective_support omega eta f p xi j _ c hc he'
  have hsupport' := projective_support omega eta f p xi k _ d hd hde'
  obtain ⟨hcards,hcube⟩ := atlas_card_invariants omega h eta f hf
  apply secant_excluded f hpar (phaseSet omega) (phaseSet_card omega h)
    (phaseSet_root omega h) hcards hcube p xi (omega ^ j.val) (omega ^ k.val)
    (phase_mem omega j) (phase_mem omega k) hphases
  · rw [hsupport]
    exact AtlasParityFrame.single_support_card omega homega _ _ _
  · rw [hsupport']
    exact AtlasParityFrame.single_support_card omega homega _ _ _
  · rw [hsupport,hsupport']
    exact AtlasParityFrame.single_support_disjoint omega homega _ _ _ _ _ (ne_of_lt pair.2)

theorem no_triangle_rich_pencil (omega : K) (h : IsPrimitiveRoot omega 3)
    (eta : Bool) (f : Signature K 6) (hpar : HasParity f)
    (hf : AtlasContractions omega eta f) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (l : TriangleLabel) (sigma : Equiv.Perm (Fin 3)) :
    ¬ RichPencil omega eta f p xi (.inr (.inr (.inr l))) sigma := by
  intro hline
  rcases l with ⟨triple,r⟩
  let j : Fin 3 := sigma.symm 0
  let k : Fin 3 := sigma.symm 1
  obtain ⟨c,hc,he⟩ := hline j
  obtain ⟨d,hd,hde⟩ := hline k
  have he' : pencil f p xi (omega ^ j.val) = c • AtlasParityFrame.table omega (eta ^^ xi)
      (twoBlock (lowerPair triple) (r 0) (r 1)) := by simpa [j,richPoints] using he
  have hde' : pencil f p xi (omega ^ k.val) = d • AtlasParityFrame.table omega (eta ^^ xi)
      (twoBlock (outerPair triple) (r 0) (r 2)) := by simpa [k,richPoints] using hde
  have hjk : j ≠ k := by
    intro h'
    have h'' := congrArg sigma h'
    simp [j,k] at h''
  have hphases := (phase_injective omega h).ne hjk
  have homega : omega ≠ 0 := cube_root_nonzero omega h.pow_eq_one
  have hsix : (jointSupport (first f p xi) (second f p xi)).card = 6 := by
    rw [joint_union_two_phases _ _ _ _ hphases,
      projective_support omega eta f p xi j _ c hc he',
      projective_support omega eta f p xi k _ d hd hde']
    have hcard := AtlasParityFrame.triangle_support_union_card omega homega (eta ^^ xi) triple r
    convert hcard using 2; ext x; simp only [Finset.mem_union]
  obtain ⟨hcards,hcube⟩ := atlas_card_invariants omega h eta f hf
  exact three_block_excluded f hpar (phaseSet omega) (phaseSet_card omega h)
    (phaseSet_root omega h) hcards hcube p xi hsix

/-- Appendix A.1(ii): no secant (1/1/2) or three-block (2/2/2) ordered
phase pencil occurs. This includes every one of the six phase assignments. -/
theorem source_A_1_ii [CharZero K] (omega : K) (h : IsPrimitiveRoot omega 3)
    (eta : Bool) (f : Signature K 6)
    (hpar : ∀ x, f x ≠ 0 → parity x = eta.toNat)
    (hf : AtlasContractions omega eta f) :
    (∀ p xi (l : SecantLabel) sigma,
      ¬ RichPencil omega eta f p xi (.inr (.inr (.inl l))) sigma) ∧
    (∀ p xi (l : TriangleLabel) sigma,
      ¬ RichPencil omega eta f p xi (.inr (.inr (.inr l))) sigma) := by
  have hp : HasParity f := fun x y hx hy => (hpar x hx).trans (hpar y hy).symm
  exact ⟨fun p xi l sigma => no_secant_rich_pencil omega h eta f hp hf p xi l sigma,
    fun p xi l sigma => no_triangle_rich_pencil omega h eta f hp hf p xi l sigma⟩

/-- The literal manuscript domain: arbitrary complex six-port tensors and
a root of `omega²+omega+1=0`. No algebraicity premise is added. -/
theorem source_A_1_ii_complex (omega : ℂ) (hpoly : omega ^ 2 + omega + 1 = 0)
    (eta : Bool) (f : Signature ℂ 6)
    (hpar : ∀ x, f x ≠ 0 → parity x = eta.toNat)
    (hf : AtlasContractions omega eta f) :
    (∀ p xi (l : SecantLabel) sigma,
      ¬ RichPencil omega eta f p xi (.inr (.inr (.inl l))) sigma) ∧
    (∀ p xi (l : TriangleLabel) sigma,
      ¬ RichPencil omega eta f p xi (.inr (.inr (.inr l))) sigma) :=
  source_A_1_ii omega (CyclotomicComplex.primitive_of_polynomial omega hpoly) eta f hpar hf

end
end Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion

