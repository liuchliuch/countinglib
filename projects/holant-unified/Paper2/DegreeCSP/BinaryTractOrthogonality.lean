import Paper2.DegreeCSP.BooleanOrthogonality
import Paper2.Paper1ProvedCriteria
import Holant.Proofs.Hardness.EOBinaryPlaneClassification

/-! Literal affine/product binary tables obey the original complex block
orthogonality conditions. This is a coefficient implication, retaining zero
entries and actual Hermitian sums, with no support-only substitute. -/
namespace Paper2.DegreeCSP.BinaryTractOrthogonality
open Tractable OriginalBO
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

private theorem proportional_self (u : Bool → ℂ) : Proportional u u :=
  ⟨1,one_ne_zero,fun j=>by simp⟩

private theorem proportional_magnitude {u v : Bool → ℂ} (h : Proportional u v) :
    MagnitudeProportional u v := by
  obtain ⟨c,hc,he⟩ := h
  refine ⟨‖c‖,norm_pos_iff.mpr hc,fun j=>?_⟩
  rw [he,norm_mul]

private theorem disjoint_not_magnitude {u v : Bool → ℂ} (hu : u≠0)
    (hd : Disjoint (support u) (support v)) : ¬MagnitudeProportional u v := by
  rintro ⟨c,hc,he⟩
  have hj : ∃j,u j≠0 := by
    by_contra hn
    push_neg at hn
    exact hu (funext hn)
  obtain ⟨j,hj⟩ := hj
  have hvj : v j=0 := by
    by_contra hn
    exact Set.disjoint_left.mp hd hj hn
  have hh := he j
  rw [hvj,norm_zero,mul_zero,norm_eq_zero] at hh
  exact hj hh

private theorem alternatives_bo (G : Bool → Bool → ℂ)
    (h : ∀x y,G x≠0 → G y≠0 →
      Proportional (G x) (G y) ∨ Disjoint (support (G x)) (support (G y))) :
    BlockOrthogonal G := by
  constructor
  · intro x y hx hy
    rcases h x y hx hy with hp|hd
    · exact Or.inl (proportional_magnitude hp)
    · exact Or.inr hd
  · intro x y hx hy hm
    rcases h x y hx hy with hp|hd
    · exact Or.inl hp
    · exact False.elim ((disjoint_not_magnitude hx hd) hm)

private theorem cross_proportional (u v : Bool → ℂ)
    (hu : u≠0) (hv : v≠0)
    (he : u false*v true=u true*v false) : Proportional u v := by
  by_cases h0 : v false=0
  · have h1 : v true≠0 := by
      intro hz
      apply hv
      funext j
      cases j <;> assumption
    have u0 : u false=0 := by
      have hz : u false*v true=0 := by simpa [h0] using he
      exact (mul_eq_zero.mp hz).resolve_right h1
    have u1 : u true≠0 := by
      intro hz
      apply hu
      funext j
      cases j <;> assumption
    refine ⟨u true/v true,div_ne_zero u1 h1,?_⟩
    intro j
    cases j
    · simp [u0,h0]
    · exact (div_mul_cancel₀ _ h1).symm
  · have u0 : u false≠0 := by
      intro hz
      have u1 : u true=0 := by
        have hh : u true*v false=0 := by simpa [hz] using he.symm
        exact (mul_eq_zero.mp hh).resolve_right h0
      apply hu
      funext j
      cases j <;> assumption
    refine ⟨u false/v false,div_ne_zero u0 h0,?_⟩
    intro j
    cases j
    · exact (div_mul_cancel₀ _ h0).symm
    · field_simp
      exact he.symm

private theorem cross_bo (G : Bool → Bool → ℂ)
    (he : G false false*G true true=G false true*G true false) : BlockOrthogonal G := by
  apply alternatives_bo
  intro x y hx hy
  left
  cases x <;> cases y
  · exact proportional_self _
  · exact cross_proportional _ _ hx hy he
  · exact cross_proportional _ _ hx hy (by linear_combination -he)
  · exact proportional_self _

private theorem diagonal_bo (G : Bool → Bool → ℂ)
    (h01 : G false true=0) (h10 : G true false=0) : BlockOrthogonal G := by
  apply alternatives_bo
  intro x y hx hy
  cases x <;> cases y
  · exact Or.inl (proportional_self _)
  · right
    apply Set.disjoint_left.mpr
    intro j hj hj'
    cases j
    · exact hj' h10
    · exact hj h01
  · right
    apply Set.disjoint_left.mpr
    intro j hj hj'
    cases j
    · exact hj h10
    · exact hj' h01
  · exact Or.inl (proportional_self _)

private theorem antidiagonal_bo (G : Bool → Bool → ℂ)
    (h00 : G false false=0) (h11 : G true true=0) : BlockOrthogonal G := by
  apply alternatives_bo
  intro x y hx hy
  cases x <;> cases y
  · exact Or.inl (proportional_self _)
  · right
    apply Set.disjoint_left.mpr
    intro j hj hj'
    cases j
    · exact hj h00
    · exact hj' h11
  · right
    apply Set.disjoint_left.mpr
    intro j hj hj'
    cases j
    · exact hj' h00
    · exact hj h11
  · exact Or.inl (proportional_self _)

private theorem negative_cross_hermitian (a b c d : ℂ) (hc : c≠0) (hd : d≠0)
    (he : a*d=-(b*c)) (hn : ‖c‖=‖d‖) : a*star c+b*star d=0 := by
  have hs : star d*d=star c*c := by
    change (starRingEnd ℂ d)*d=(starRingEnd ℂ c)*c
    rw [Complex.conj_mul',Complex.conj_mul',hn]
  apply (mul_right_cancel₀ (mul_ne_zero hc hd))
  calc
    _ = a*d*(star c*c)+b*c*(star d*d) := by ring
    _ = (a*d+b*c)*(star c*c) := by rw [hs]; ring
    _ = 0*(c*d) := by rw [he]; ring

private theorem equal_norm_negative_bo (G : Bool → Bool → ℂ)
    (hne : ∀i j,G i j≠0) (hn : ∀i j,‖G i j‖=‖G false false‖)
    (he : G false false*G true true=-(G false true*G true false)) : BlockOrthogonal G := by
  have hinner : G false false*star (G true false)+G false true*star (G true true)=0 :=
    negative_cross_hermitian _ _ _ _ (hne _ _) (hne _ _) he ((hn _ _).trans (hn _ _).symm)
  have hreverse : G true false*star (G false false)+G true true*star (G false true)=0 := by
    have hs := congrArg star hinner
    simpa only [star_add,star_mul,star_star,star_zero,mul_comm] using hs
  have allmag (i j : Bool) : MagnitudeProportional (G i) (G j) :=
    ⟨1,by norm_num,fun b=>by simp only [one_mul]; exact (hn i b).trans (hn j b).symm⟩
  have orth (i j : Bool) (h : G i false*star (G j false)+G i true*star (G j true)=0) :
      VectorBlockOrthogonal (G i) (G j) := by
    intro z hz
    have hb : magnitudeBlock (G i) z=Finset.univ := by
      ext w
      simp [magnitudeBlock,(hn i w).trans (hn i z).symm]
    rw [hb]
    simpa [hermitianSum,Fintype.sum_bool,add_comm] using h
  refine ⟨fun i j _ _=>Or.inl (allmag i j),?_⟩
  intro i j hi hj hm
  cases i <;> cases j
  · exact Or.inl (proportional_self _)
  · exact Or.inr (orth _ _ hinner)
  · exact Or.inr (orth _ _ hreverse)
  · exact Or.inl (proportional_self _)

theorem product_binary_bo (f : Signature AlgebraicComplex 2) (hf : Product f) :
    BlockOrthogonal (fun b c : Bool=>(f ![b,c] : ℂ)) := by
  have h : Holant.Tractable.SymmetricBinaryPullback.ProductShape
      (Holant.Tractable.SymmetricBinaryPullback.table f) := by
    have hf' := (Paper2.Paper1Proved.product_iff f).mp hf
    have he := Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification.kernel_table f
    exact Holant.Tractable.SymmetricBinaryPullback.product_shape (by rwa [he])
  rcases h with h|h|h
  · exact diagonal_bo _ (by exact_mod_cast h.1) (by exact_mod_cast h.2)
  · exact antidiagonal_bo _ (by exact_mod_cast h.1) (by exact_mod_cast h.2)
  · exact cross_bo _ (by exact_mod_cast h)

theorem affine_binary_bo (f : Signature AlgebraicComplex 2) (hf : Affine f) :
    BlockOrthogonal (fun b c : Bool=>(f ![b,c] : ℂ)) := by
  classical
  have hf' := (Paper2.Paper1Proved.affine_iff f).mp hf
  by_cases hfull : ∀x,f x≠0
  · obtain ⟨hfour,hcross⟩ :=
      (Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification.full_affine_iff f hfull).mp hf'
    rcases hcross with hc|hc
    · exact cross_bo _ (by exact_mod_cast hc)
    · apply equal_norm_negative_bo
      · intro b c
        exact_mod_cast hfull ![b,c]
      · intro b c
        have he := congrArg (fun z : AlgebraicComplex=>‖(z : ℂ)‖) (hfour ![b,c])
        change ‖((f ![b,c] : ℂ)^4)‖=‖((f ![false,false] : ℂ)^4)‖ at he
        simp only [norm_pow] at he
        exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by decide : (4 : ℕ)≠0)).mp he
      · exact_mod_cast hc
  · have hsmall : (Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseTract.support f).card≤2 := by
      have hsub : Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseTract.support f ⊂ Finset.univ := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.subset_univ _,?_⟩
        intro he
        apply hfull
        intro x
        have hm : x∈Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseTract.support f := by rw [he]; simp
        simpa only [Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseTract.mem_support] using hm
      have hc := Finset.card_lt_card hsub
      have hu : (Finset.univ : Finset (Fin 2→Bool)).card=4 := by decide
      rw [hu] at hc
      have hn : (Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseTract.support f).card≠3 := by
        intro hthree
        exact Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification.three_not_affine f hthree hf'
      omega
    exact product_binary_bo f ((Paper2.Paper1Proved.product_iff f).mpr
      (Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseTract.binary_small f hsmall))

theorem binary_tract_bo (f : Signature AlgebraicComplex 2) (hf : Affine f ∨ Product f) :
    BlockOrthogonal (fun b c : Bool=>(f ![b,c] : ℂ)) :=
  hf.elim (affine_binary_bo f) (product_binary_bo f)

theorem not_binary_tract_of_not_bo (f : Signature AlgebraicComplex 2)
    (h : ¬BlockOrthogonal (fun b c : Bool=>(f ![b,c] : ℂ))) : ¬Affine f ∧ ¬Product f :=
  ⟨fun hf=>h (affine_binary_bo f hf),fun hf=>h (product_binary_bo f hf)⟩

theorem lift_not_eoTract (f : Signature AlgebraicComplex 2)
    (h : ¬BlockOrthogonal (fun b c : Bool=>(f ![b,c] : ℂ))) :
    ¬Holant.Tractable.EOTract {⟨4,Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore.lift f⟩} := by
  rw [Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneTract.lift_tract_iff]
  intro hf
  apply h
  apply binary_tract_bo f
  exact hf.imp (Paper2.Paper1Proved.affine_iff f).mpr (Paper2.Paper1Proved.product_iff f).mpr

end
end Paper2.DegreeCSP.BinaryTractOrthogonality
