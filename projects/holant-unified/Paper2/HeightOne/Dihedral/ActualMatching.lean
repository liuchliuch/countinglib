import Paper2.HeightOne.PhaseCards.OrientedMenu
import Paper2.HeightOne.Cyclic.ProductCards
import Paper2.HeightOne.Dihedral.BinaryComplement

/-! Matching-coset support and coefficient Product structure of every actual
minimum-prime xor card. All local binary factors come from the real retained
selected decomposition; no support deck is assumed. -/
namespace Paper2.HeightOne.Dihedral
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Tractable ExactInput PhaseCards Cyclic GroupSplit GroupSplit.MatrixGroup EndpointSelfLoop
open scoped BigOperators

lemma normalized_binary_xor_support {F : SignatureFamily AlgebraicComplex} {N : ℕ}
    (hG : actualClasses F = dihedralPhaseClasses N) {B : AMat}
    (hB : ActualNonsingular F B) :
    ∃ d : Bool, ∀ x : Fin 2 → Bool,
      walshCoordinates (binarySignature B) x ≠ 0 ↔ Bool.xor (x 0) (x 1) = d := by
  rcases actual_binary_phase_shape (Or.inr hG) hB with ⟨s,c,hc,he⟩ | ⟨s,c,hc,he⟩
  · refine ⟨false, ?_⟩
    intro x
    rw [walshCoordinates_binary, rotation_walsh_binary he]
    cases hx0 : x 0 <;> cases hx1 : x 1 <;>
      simp [binarySignature, PhaseCards.plusKernel, hx0, hx1, hc, Units.ne_zero s.val]
  · refine ⟨true, ?_⟩
    intro x
    rw [walshCoordinates_binary, reflection_walsh_binary he]
    cases hx0 : x 0 <;> cases hx1 : x 1 <;>
      simp [binarySignature, reflectedBinary, hx0, hx1, hc, Units.ne_zero s.val]

lemma normalized_signature_xor_support {F : SignatureFamily AlgebraicComplex} {N n : ℕ}
    (hG : actualClasses F = dihedralPhaseClasses N) (hsafe : AllBinariesSafe F)
    (f : Signature AlgebraicComplex n) (hn : n = 2)
    (hf : NetworkRealizable F f) (hfn : f ≠ 0) :
    ∃ d : Bool, ∀ x, walshCoordinates f x ≠ 0 ↔
      Bool.xor (x (Fin.cast hn.symm 0)) (x (Fin.cast hn.symm 1)) = d := by
  subst n
  simpa only [binarySignature_tableBinary, Fin.cast_refl, id_eq] using
    normalized_binary_xor_support hG (actual_tableBinary hsafe f hf hfn)

lemma decomposition_matching_coset {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (htwo : ∀ i, D.arity i = 2)
    (d : Fin D.count → Bool)
    (hfactor : ∀ i x, D.factor i x ≠ 0 ↔
      Bool.xor (x (Fin.cast (htwo i).symm 0)) (x (Fin.cast (htwo i).symm 1)) = d i) :
    support D.value = Finset.univ.image (Matching.word (decompositionPairing D htwo) d) := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  rw [← Matching.pair_constraints_iff_word, mem_support]
  simp only [TensorDecomposition.value, mul_ne_zero_iff,
    Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const, hfactor]
  exact and_iff_right (Units.ne_zero D.scale)

/-- A perfect matching coset includes its actual independent pair offsets. -/
def MatchingCosetSupport {ι : Type} [Fintype ι] (f : Tensor AlgebraicComplex ι) : Prop :=
  ∃ (P : Pairing (Fintype.card ι)) (d : Fin P.count → Bool),
    support (Tensor.reindex (Fintype.equivFin ι) f) = Finset.univ.image (Matching.word P d)

/-- Each real selected card has both its exact matching support and all its
Product rectangle equations in the one Walsh coordinate system. -/
theorem minimum_card_walsh_coset {F : SignatureFamily AlgebraicComplex}
    (M : BinaryMenu F) (L : Language) (heven : ∀ f ∈ L.family, Even f.1)
    (hsafe : AllBinariesSafe L.family) {N n : ℕ}
    (hG : actualClasses L.family = dihedralPhaseClasses N) (hmin : LeastPrimeArity L.family n)
    (f : AnySignature AlgebraicComplex) (hf : f.1 = n) (hprocessed : M.Processed f L)
    (k : M.Choices f) (hcard : 0 < (M.produced f k).1 ∧ (M.produced f k).2 ≠ 0) :
    ∃ (P : Pairing (M.produced f k).1) (d : Fin P.count → Bool),
      support (walshCoordinates (M.produced f k).2) = Finset.univ.image (Matching.word P d) := by
  let Q := selectedDecomposition (M.produced f k) hcard
  have hQ := selectedDecomposition_spec (M.produced f k) hcard
  have hc (i : Fin Q.count) : (⟨Q.arity i, Q.factor i⟩ : AnySignature AlgebraicComplex) ∈ M.children f := by
    apply Set.mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [selectedFactors, dif_pos hcard]
    exact ⟨i, rfl⟩
  have hmem := fun i => hprocessed.2.1 (hc i)
  have htwo : ∀ i, Q.arity i = 2 := fun i =>
    selected_card_factors_binary M L heven hmin f hf hprocessed (hc i)
  have hd : ∀ i, ∃ d : Bool, ∀ x, walshCoordinates (Q.factor i) x ≠ 0 ↔
      Bool.xor (x (Fin.cast (htwo i).symm 0)) (x (Fin.cast (htwo i).symm 1)) = d := by
    intro i
    exact normalized_signature_xor_support hG hsafe (Q.factor i) (htwo i)
      (networkRealizable_of_mem (hmem i)) (hQ.2.2 i).1
  choose d hd using hd
  let R := Q.mapAction walshInv
  have hR : ∀ i, R.arity i = 2 := htwo
  have hs := decomposition_matching_coset R hR d (fun i x => by
    simpa only [R, TensorDecomposition.mapAction, ← walshCoordinates_eq_coordinateAction] using hd i x)
  have he := (TensorDecomposition.value_mapAction Q walshInv).trans
    (walshCoordinates_eq_coordinateAction Q.value).symm
  rw [he, hQ.1] at hs
  exact ⟨decompositionPairing R hR, d, hs⟩

variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]

/-- The selected actual xor representative is precisely the representative
processed by the finite saturation. Nonzero scalar cancellation is analytic. -/
theorem minimum_xorCard_product (C : XorCards F N) (L : Language)
    (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hG : actualClasses L.family = dihedralPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n)
    (hprocessed : (xorMenu C).Processed ⟨n,f⟩ L)
    (a b : Fin n) (hab : a ≠ b) (u v : Bool) (s : rootsOfUnity N AlgebraicComplex) :
    Product (Tensor.reindex (Fintype.equivFin (Remaining a b))
      (card (xorKernel u v s.val) a b hab (walshCoordinates f))) := by
  classical
  let k := xorChoice C f a b hab u v s
  let g := (xorMenu C).produced ⟨n,f⟩ k
  have hw := xor_produced_walsh C f a b hab u v s
  change walshCoordinates g.2 = _ at hw
  by_cases hn : g.2 = 0
  · apply Or.inl
    rw [hn, walsh_zero] at hw
    funext x
    exact (mul_eq_zero.mp (congrFun hw x).symm).resolve_left (C.scale_ne_zero u v s)
  have hp : 0 < g.1 := by
    have ha := (xorMenu C).produced_arity ⟨n,f⟩ k
    have h3 := hmin.ge_three
    change g.1 + 2 = n at ha
    omega
  have hprod := minimum_card_walsh_product (xorMenu C) L heven hsafe (Or.inr hG) hmin
    ⟨n,f⟩ rfl hprocessed k ⟨hp,hn⟩
  rw [hw] at hprod
  have hh := hprod.scale (C.scale u v s)⁻¹
  simpa only [Pi.smul_apply, smul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ (C.scale_ne_zero u v s), one_mul] using hh

/-- Matching support of the analytic xor card, obtained from its actual
retained binary prime factors rather than an assumed support certificate. -/
theorem minimum_xorCard_coset (C : XorCards F N) (L : Language)
    (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hG : actualClasses L.family = dihedralPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n)
    (hprocessed : (xorMenu C).Processed ⟨n,f⟩ L)
    (a b : Fin n) (hab : a ≠ b) (u v : Bool) (s : rootsOfUnity N AlgebraicComplex)
    (hn : card (xorKernel u v s.val) a b hab (walshCoordinates f) ≠ 0) :
    MatchingCosetSupport (card (xorKernel u v s.val) a b hab (walshCoordinates f)) := by
  classical
  let k := xorChoice C f a b hab u v s
  let g := (xorMenu C).produced ⟨n,f⟩ k
  have hw := xor_produced_walsh C f a b hab u v s
  change walshCoordinates g.2 = _ at hw
  have hgn : g.2 ≠ 0 := by
    intro hz
    rw [hz, walsh_zero] at hw
    apply hn
    funext x
    have he := congrFun hw (fun j => x ((Fintype.equivFin (Remaining a b)).symm j))
    have hh : C.scale u v s * card (xorKernel u v s.val) a b hab (walshCoordinates f) x = 0 := by
      simpa only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, Tensor.reindex_apply,
        Equiv.symm_apply_apply] using he.symm
    exact (mul_eq_zero.mp hh).resolve_left (C.scale_ne_zero u v s)
  have hp : 0 < g.1 := by
    have ha := (xorMenu C).produced_arity ⟨n,f⟩ k
    have h3 := hmin.ge_three
    change g.1 + 2 = n at ha
    omega
  obtain ⟨P,d,he⟩ := minimum_card_walsh_coset (xorMenu C) L heven hsafe hG hmin
    ⟨n,f⟩ rfl hprocessed k ⟨hp,hgn⟩
  rw [hw, support_smul _ (C.scale_ne_zero u v s)] at he
  exact ⟨P,d,he⟩

end
end Paper2.HeightOne.Dihedral

