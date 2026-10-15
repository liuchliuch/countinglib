import Paper2.Paper1ProvedPinCoordinate
import Paper2.Paper1ProvedOddUnaryIsotropic
import Paper2.NetworkSubstitution

/-! Both literal native unit pins retain an adjacent pair of nonzero
support entries as the two entries of an actual capped unary. Its inverse
chart has a nonzero ordinary bilinear norm. The conclusion is a native
network over the retained language, with no original-label claim inferred
from an arbitrary controlled reduction. -/
namespace Paper2.Paper1Proved.OddUnary.Adjacent
open Paper2.Tractable Paper2.ExactInput
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
noncomputable section
set_option backward.isDefEq.respectTransparency false

def adjacently_supported {K : Type*} [Zero K] {n : ℕ} (f : Signature K n) : Prop :=
  ∃ i : Fin n, ∃ x : Fin n → Bool, f x ≠ 0 ∧ f (Function.update x i (!(x i))) ≠ 0

theorem coordinate_entries {n : ℕ} (f : Signature AlgebraicComplex n)
    (i : Fin n) (x : Fin n → Bool) (hx : f x ≠ 0)
    (hflip : f (Function.update x i (!(x i))) ≠ 0) :
    PinCoordinate.coordinateUnary f i x (fun _ => false) ≠ 0 ∧
      PinCoordinate.coordinateUnary f i x (fun _ => true) ≠ 0 := by
  have he := Function.update_eq_self i x
  cases hb : x i
  · have h0 : Function.update x i false=x := by simpa only [hb] using he
    constructor
    · simpa only [PinCoordinate.coordinateUnary,h0] using hx
    · simpa only [PinCoordinate.coordinateUnary,hb,Bool.not_false] using hflip
  · have h1 : Function.update x i true=x := by simpa only [hb] using he
    constructor
    · simpa only [PinCoordinate.coordinateUnary,hb,Bool.not_true] using hflip
    · simpa only [PinCoordinate.coordinateUnary,h1] using hx

theorem adjacently_supported_iff {n : ℕ} (f : Signature AlgebraicComplex n) :
    adjacently_supported f ↔ ∃ i : Fin n, ∃ x : Fin n → Bool,
      PinCoordinate.coordinateUnary f i x (fun _ => false) ≠ 0 ∧
        PinCoordinate.coordinateUnary f i x (fun _ => true) ≠ 0 := by
  constructor
  · rintro ⟨i,x,hx,hflip⟩
    exact ⟨i,x,coordinate_entries f i x hx hflip⟩
  · rintro ⟨i,x,h0,h1⟩
    refine ⟨i,Function.update x i false,h0,?_⟩
    simpa only [Function.update_self,Bool.not_false,Function.update_idem,
      PinCoordinate.coordinateUnary] using h1

/-- The residual support condition is the literal product-zero test used by
the ternary coefficient analysis. It retains possible zero entries exactly. -/
theorem not_adjacently_supported_iff {n : ℕ} (f : Signature AlgebraicComplex n) :
    ¬ adjacently_supported f ↔ ∀ (i : Fin n) (x : Fin n → Bool),
      f (Function.update x i false)*f (Function.update x i true)=0 := by
  constructor
  · intro ha i x
    by_contra hn
    have h := mul_ne_zero_iff.mp hn
    apply ha
    exact (adjacently_supported_iff f).mpr ⟨i,x,h⟩
  · intro h ha
    obtain ⟨i,x,h0,h1⟩ := (adjacently_supported_iff f).mp ha
    exact mul_ne_zero h0 h1 (h i x)

theorem ordinary_norm (u : Signature AlgebraicComplex 1) :
    GeneralOddNonisotropicFrame.norm (Holant.Tractable.sourceKBasis.action u) =
      2*u (fun _ => false)*u (fun _ => true) := by
  rw [Isotropic.norm_eq_pairing,GeneralOddUnaryOrdinary.pairing_action]
  ring

theorem ordinary_norm_ne_zero (u : Signature AlgebraicComplex 1)
    (h0 : u (fun _ => false) ≠ 0) (h1 : u (fun _ => true) ≠ 0) :
    GeneralOddNonisotropicFrame.norm (Holant.Tractable.sourceKBasis.action u) ≠ 0 := by
  rw [ordinary_norm]
  exact mul_ne_zero (mul_ne_zero (by norm_num) h0) h1

theorem capped_unary (N : Language) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (i : Fin n) (x : Fin n → Bool) (hx : f x ≠ 0)
    (hflip : f (Function.update x i (!(x i))) ≠ 0) :
    ∃ u : Signature AlgebraicComplex 1,
      NetworkRealizable N.family u ∧ u (fun _ => false) ≠ 0 ∧ u (fun _ => true) ≠ 0 ∧
      GeneralOddNonisotropicFrame.norm (Holant.Tractable.sourceKBasis.action u) ≠ 0 := by
  let u := PinCoordinate.coordinateUnary f i x
  have hu := PinCoordinate.coordinateUnary_realizable N f i x hf h0 h1
  obtain ⟨hu0,hu1⟩ := coordinate_entries f i x hx hflip
  exact ⟨u,hu,hu0,hu1,ordinary_norm_ne_zero u hu0 hu1⟩

theorem capped_unary_of_adjacently_supported (N : Language) {n : ℕ}
    (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (ha : adjacently_supported f) :
    ∃ u : Signature AlgebraicComplex 1,
      NetworkRealizable N.family u ∧ u (fun _ => false) ≠ 0 ∧ u (fun _ => true) ≠ 0 ∧
      GeneralOddNonisotropicFrame.norm (Holant.Tractable.sourceKBasis.action u) ≠ 0 := by
  obtain ⟨i,x,hx,hflip⟩ := ha
  exact capped_unary N f hf h0 h1 i x hx hflip

/-- Inline the actual graph for the capped signature. Every other vertex is
one of the original unit pins, so the resulting unary uses the original
resource family itself. -/
theorem coordinateUnary_realizable_of_realizable (N : Language) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hgraph : NetworkRealizable N.family f)
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (i : Fin n) (x : Fin n → Bool) :
    NetworkRealizable N.family (PinCoordinate.coordinateUnary f i x) := by
  let F : SignatureFamily AlgebraicComplex := Set.insert ⟨n,f⟩ N.family
  have hc := PinCoordinate.coordinateUnary_realizable_family F f i x
    (Set.mem_insert _ _) (Set.mem_insert_of_mem _ h0) (Set.mem_insert_of_mem _ h1)
  apply hc.trans
  rintro g (rfl | hg)
  · exact hgraph
  · refine ⟨g.1,Paper2.Network.corolla g.2,Equiv.refl _,?_,?_,?_⟩
    · intro v
      exact hg
    · intro e
      exact Fin.elim0 e
    · simp only [Tensor.reindex_refl,Paper2.Network.denote_corolla]

theorem capped_unary_of_realizable (N : Language) {n : ℕ}
    (f : Signature AlgebraicComplex n) (hgraph : NetworkRealizable N.family f)
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (ha : adjacently_supported f) :
    ∃ u : Signature AlgebraicComplex 1,
      NetworkRealizable N.family u ∧ u (fun _ => false) ≠ 0 ∧ u (fun _ => true) ≠ 0 ∧
      GeneralOddNonisotropicFrame.norm (Holant.Tractable.sourceKBasis.action u) ≠ 0 := by
  obtain ⟨i,x,hx,hflip⟩ := ha
  obtain ⟨hu0,hu1⟩ := coordinate_entries f i x hx hflip
  exact ⟨PinCoordinate.coordinateUnary f i x,
    coordinateUnary_realizable_of_realizable N f hgraph h0 h1 i x,
    hu0,hu1,ordinary_norm_ne_zero _ hu0 hu1⟩

theorem no_adjacent_of_isotropic_caps (N : Language)
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (hiso : ∀ u : Signature AlgebraicComplex 1, NetworkRealizable N.family u →
      GeneralOddNonisotropicFrame.norm (Holant.Tractable.sourceKBasis.action u)=0) :
    ∀ f ∈ N.family, ¬ adjacently_supported f.2 := by
  rintro ⟨n,f⟩ hf ha
  obtain ⟨u,hu,_,_,hn⟩ := capped_unary_of_adjacently_supported N f hf h0 h1 ha
  exact hn (hiso u hu)

theorem no_adjacent_realizable_of_isotropic_caps (N : Language)
    (h0 : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (h1 : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (hiso : ∀ u : Signature AlgebraicComplex 1, NetworkRealizable N.family u →
      GeneralOddNonisotropicFrame.norm (Holant.Tractable.sourceKBasis.action u)=0)
    {n : ℕ} (f : Signature AlgebraicComplex n) (hgraph : NetworkRealizable N.family f) :
    ¬ adjacently_supported f := by
  intro ha
  obtain ⟨u,hu,_,_,hn⟩ := capped_unary_of_realizable N f hgraph h0 h1 ha
  exact hn (hiso u hu)

end
end Paper2.Paper1Proved.OddUnary.Adjacent
