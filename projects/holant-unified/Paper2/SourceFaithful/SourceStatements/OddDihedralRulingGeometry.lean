import Paper2.SourceFaithful.SourceStatements.OddDihedralPencilStatement
import Paper2.Certificates.DihedralSupport.AtlasParityFrameGeometry
import Paper2.Certificates.DihedralSupport.AtlasRulingFactors

/-! The entire coefficient span of a rich contraction pencil lies on its
specified atlas line. A Segre ruling retains one literal fixed factor for
every linear combination of the two original slices. -/
namespace Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
open Paper2.HeightOne Paper2.HeightOne.Dihedral SixPortPencils
open Paper2.Certificates.DihedralSupport AtlasCounts AtlasVectors
noncomputable section
set_option maxRecDepth 4096

variable {K : Type} [Field K]

theorem slices_interpolation (f : Signature K 6) (p : Equiv.Perm (Fin 6))
    (xi : Bool) (s t alpha beta : K) (hst : s ≠ t) :
    alpha • first f p xi + beta • second f p xi =
      ((alpha*t+beta)/(t-s)) • pencil f p xi s +
      ((-alpha*s-beta)/(t-s)) • pencil f p xi t := by
  have hts : t-s ≠ 0 := sub_ne_zero.mpr hst.symm
  funext r
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,pencil]
  field_simp [hts]
  ring

/-- The span uses the actual first two atlas points of the typed line,
independently of the phase-to-point assignment. -/
theorem richPencil_coefficient_span (omega : K) (h : IsPrimitiveRoot omega 3)
    (eta : Bool) (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (line : RichLabel) (sigma : Equiv.Perm (Fin 3))
    (hp : RichPencil omega eta f p xi line sigma) (alpha beta : K) :
    alpha • first f p xi + beta • second f p xi ∈ Submodule.span K
      ({AtlasParityFrame.table omega (eta ^^ xi) (richPoints line 0),
        AtlasParityFrame.table omega (eta ^^ xi) (richPoints line 1)} :
        Set (Signature K 4)) := by
  let j : Fin 3 := sigma.symm 0
  let k : Fin 3 := sigma.symm 1
  obtain ⟨c,hc,he⟩ := hp j
  obtain ⟨d,hd,ht⟩ := hp k
  have he' : pencil f p xi (omega^j.val) =
      c • AtlasParityFrame.table omega (eta ^^ xi) (richPoints line 0) := by
    simpa only [j,Equiv.apply_symm_apply] using he
  have ht' : pencil f p xi (omega^k.val) =
      d • AtlasParityFrame.table omega (eta ^^ xi) (richPoints line 1) := by
    simpa only [k,Equiv.apply_symm_apply] using ht
  have hjk : j ≠ k := sigma.symm.injective.ne (by decide)
  have hst := (phase_injective omega h).ne hjk
  have hh := slices_interpolation f p xi (omega^j.val) (omega^k.val) alpha beta hst
  rw [he',ht',smul_smul,smul_smul] at hh
  exact Submodule.mem_span_pair.mpr ⟨_,_,hh.symm⟩

def frameCoefficients (epsilon : Bool) (f : Signature K 4) : Coordinate → K :=
  fun c => f (AtlasParityFrame.word epsilon c)

theorem richPencil_frame_span (omega : K) (h : IsPrimitiveRoot omega 3)
    (eta : Bool) (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (line : RichLabel) (sigma : Equiv.Perm (Fin 3))
    (hp : RichPencil omega eta f p xi line sigma) (alpha beta : K) :
    frameCoefficients (eta ^^ xi) (alpha • first f p xi + beta • second f p xi) ∈
      Submodule.span K ({vector omega (richPoints line 0),
        vector omega (richPoints line 1)} : Set (Coordinate → K)) := by
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp
    (richPencil_coefficient_span omega h eta f p xi line sigma hp alpha beta)
  refine Submodule.mem_span_pair.mpr ⟨a,b,?_⟩
  funext c
  have hh := congrFun hab (AtlasParityFrame.word (eta ^^ xi) c)
  simpa only [Pi.add_apply,Pi.smul_apply,AtlasParityFrame.table_word,frameCoefficients]
    using hh

/-- Every vector in the original two-slice coefficient span has the same
fixed Segre factor; the varying factor may vanish for the zero vector. -/
theorem richPencil_fixed_ruling (omega : K) (h : IsPrimitiveRoot omega 3)
    (eta : Bool) (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (line : RulingLabel) (sigma : Equiv.Perm (Fin 3))
    (hp : RichPencil omega eta f p xi (.inr (.inl line)) sigma) (alpha beta : K) :
    AtlasRulingFactors.FixedRuling omega line
      (frameCoefficients (eta ^^ xi) (alpha • first f p xi + beta • second f p xi)) :=
  AtlasRulingFactors.span_fixedRuling omega h.pow_eq_one line _
    (richPencil_frame_span omega h eta f p xi (.inr (.inl line)) sigma hp alpha beta)

/-- One-block pencils retain the same two complementary word positions
throughout the entire original coefficient span. -/
theorem richPencil_one_block (omega : K) (h : IsPrimitiveRoot omega 3)
    (eta : Bool) (f : Signature K 6) (p : Equiv.Perm (Fin 6)) (xi : Bool)
    (line : OneBlockLabel) (sigma : Equiv.Perm (Fin 3))
    (hp : RichPencil omega eta f p xi (.inl line) sigma) (alpha beta : K)
    (x : Fin 4 → Bool) (hx : (AtlasParityFrame.coordinates x).1 ≠ line) :
    (alpha • first f p xi + beta • second f p xi) x = 0 := by
  obtain ⟨a,b,hab⟩ := Submodule.mem_span_pair.mp
    (richPencil_coefficient_span omega h eta f p xi (.inl line) sigma hp alpha beta)
  have hh := congrFun hab x
  simpa [AtlasParityFrame.table,AtlasParityFrame.extendVector,richPoints,
    vector,single,singleVector,hx] using hh.symm

end
end Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion

