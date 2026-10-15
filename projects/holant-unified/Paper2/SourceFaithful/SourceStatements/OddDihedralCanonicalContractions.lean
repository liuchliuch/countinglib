import Paper2.SourceFaithful.SourceStatements.OddDihedralCanonicalPencil
import Paper2.SourceFaithful.SourceStatements.OddDihedralPencilConsequence
import Paper2.Certificates.DihedralSupport.SixPortCanonicalPairs
import Paper2.Certificates.DihedralSupport.AtlasPermutation

/-! Appendix A.1(ii) with precisely the fifteen increasing-order port pairs
used in the manuscript. Residual permutations act on the literal 66-point
atlas. Reversing the selected pair retains the actual inverse phase and
common scalar; no additional ordered-pair hypothesis is imposed. -/
namespace Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
open Paper2.HeightOne Paper2.HeightOne.Dihedral SixPortSupport SixPortPencils
open Paper2.Certificates.DihedralSupport AtlasCounts
noncomputable section
set_option maxRecDepth 4096

variable {K : Type} [Field K]

/-- The exclusions and the ensuing one-block-or-Segre-ruling classification
of every nonconstant pencil, including every phase assignment. -/
structure PencilStatement (omega : K) (eta : Bool) (f : Signature K 6) : Prop where
  secant : ∀ p xi (l : SecantLabel) sigma,
    ¬ RichPencil omega eta f p xi (.inr (.inr (.inl l))) sigma
  triangle : ∀ p xi (l : TriangleLabel) sigma,
    ¬ RichPencil omega eta f p xi (.inr (.inr (.inr l))) sigma
  nonconstant : ∀ p xi,
    LinearIndependent K ![first f p xi,second f p xi] →
      (∃ l : OneBlockLabel, ∃ sigma : Equiv.Perm (Fin 3),
        RichPencil omega eta f p xi (.inl l) sigma) ∨
      (∃ l : RulingLabel, ∃ sigma : Equiv.Perm (Fin 3),
        RichPencil omega eta f p xi (.inr (.inl l)) sigma)

theorem canonicalContractions_of_atlas (omega : K) (eta : Bool) (f : Signature K 6)
    (hf : AtlasContractions omega eta f) : CanonicalAtlasContractions omega eta f := by
  intro q xi j
  have he : pencil f (SixPortCanonicalPairs.canonical q) xi (omega^j.val) =
      canonicalPencil f q xi (omega^j.val) := by
    funext r
    simp only [pencil,first,second,SixPortCanonicalPairs.canonical_lift,canonicalPencil]
  rw [← he]
  exact hf (SixPortCanonicalPairs.canonical q) xi j

/-- All ordered slices follow from the literal fifteen unordered slices.
The proof transports actual coefficients, rather than only their support. -/
theorem atlasContractions_of_canonical [CharZero K] (omega : K)
    (hpoly : omega ^ 2 + omega + 1 = 0) (eta : Bool) (f : Signature K 6)
    (hf : CanonicalAtlasContractions omega eta f) : AtlasContractions omega eta f := by
  intro p xi j
  obtain ⟨q,flag,e,he⟩ := SixPortCanonicalPairs.exists_lift_reindex p
  let s := omega ^ j.val
  have hs : s ^ 3 = 1 := by
    dsimp [s]
    rw [← pow_mul,Nat.mul_comm j.val 3,pow_mul,
      (CyclotomicComplex.primitive_of_polynomial omega hpoly).pow_eq_one,one_pow]
  have hsne : s ≠ 0 := cube_root_nonzero s hs
  cases hb : flag && xi
  · have hp : pencil f p xi s = Tensor.reindex e (canonicalPencil f q xi s) := by
      funext r
      simp only [pencil,first,second,Tensor.reindex_apply,canonicalPencil]
      rw [he xi false r,he xi true r]
      simp [hb]
    change AtlasParityFrame.Admissible omega (eta ^^ xi) (pencil f p xi s)
    rw [hp]
    exact AtlasPermutation.admissible_reindex omega hpoly _ _ (hf q xi j) e
  · have hp : pencil f p xi s = Tensor.reindex e
        (fun r => f (liftWord q xi true r) - s * f (liftWord q xi false r)) := by
      funext r
      simp only [pencil,first,second,Tensor.reindex_apply]
      rw [he xi false r,he xi true r]
      simp [hb]
    have hi : (s⁻¹) ^ 3 = 1 := by rw [inv_pow,hs,inv_one]
    have hc := canonical_admissible_root omega hpoly eta f hf q xi s⁻¹ hi
    have hr := AtlasPermutation.admissible_reindex omega hpoly _ _ hc e
    change AtlasParityFrame.Admissible omega (eta ^^ xi) (pencil f p xi s)
    rw [hp,canonical_pencil_reversed f q xi s hsne]
    change AtlasParityFrame.Admissible omega (eta ^^ xi)
      ((-s) • Tensor.reindex e (canonicalPencil f q xi s⁻¹))
    exact admissible_smul omega _ _ hr (-s)

/-- The literal Appendix A.1(ii) statement, over any characteristic-zero
field, with only the manuscript's fifteen increasing-order pairs. -/
theorem source_A_1_ii_literal [CharZero K] (omega : K)
    (hpoly : omega ^ 2 + omega + 1 = 0) (eta : Bool) (f : Signature K 6)
    (hpar : ∀ x, f x ≠ 0 → parity x = eta.toNat)
    (hf : CanonicalAtlasContractions omega eta f) : PencilStatement omega eta f := by
  have ha := atlasContractions_of_canonical omega hpoly eta f hf
  obtain ⟨hsec,htri⟩ := source_A_1_ii omega
    (CyclotomicComplex.primitive_of_polynomial omega hpoly) eta f hpar ha
  exact ⟨hsec,htri,fun p xi hn =>
    source_A_1_ii_consequence omega hpoly eta f hpar ha p xi hn⟩

/-- No algebraicity restriction is added to the manuscript's arbitrary
complex six-port tensor. -/
theorem source_A_1_ii_literal_complex (omega : ℂ)
    (hpoly : omega ^ 2 + omega + 1 = 0) (eta : Bool) (f : Signature ℂ 6)
    (hpar : ∀ x, f x ≠ 0 → parity x = eta.toNat)
    (hf : CanonicalAtlasContractions omega eta f) : PencilStatement omega eta f :=
  source_A_1_ii_literal omega hpoly eta f hpar hf

end
end Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion

