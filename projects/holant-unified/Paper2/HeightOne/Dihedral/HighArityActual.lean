import Paper2.HeightOne.Dihedral.ActualMatching
import Paper2.HeightOne.Dihedral.HighArityRigidity

/-! Actual minimum-prime cards carry full nonsingular monomial matching
presentations in Walsh coordinates. The exact selected decomposition retains
every binary coefficient, ordered port and nonzero scalar. -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Tractable ExactInput PhaseCards Cyclic GroupSplit GroupSplit.MatrixGroup
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

theorem normalized_walsh_monomial {F : SignatureFamily AlgebraicComplex} {N n : ℕ}
    (hG : actualClasses F = dihedralPhaseClasses N) (hsafe : AllBinariesSafe F)
    (f : Signature AlgebraicComplex n) (hn : n = 2)
    (hf : NetworkRealizable F f) (hfn : f ≠ 0) :
    Holant.Marked.IsMonomial (fun a b => walshCoordinates f (fun j => if j.val = 0 then a else b)) := by
  subst n
  have hB := actual_tableBinary hsafe f hf hfn
  have hv (a b : Bool) : (fun j : Fin 2 => if j.val = 0 then a else b) = ![a,b] := by
    funext j
    fin_cases j <;> rfl
  rw [← binarySignature_tableBinary f]
  simp only [walshCoordinates_binary,hv,binarySignature]
  rcases actual_binary_phase_shape (Or.inr hG) hB with ⟨s,c,hc,he⟩ | ⟨s,c,hc,he⟩
  · rw [rotation_walsh_binary he]
    refine ⟨false,fun a => (c / 2) * (if a then -s.val else 1),?_,?_⟩
    · intro a
      cases a <;> simp [hc,Units.ne_zero s.val]
    · funext a b
      cases a <;> cases b <;> simp [PhaseCards.plusKernel,Holant.Marked.monomial]
  · rw [reflection_walsh_binary he]
    refine ⟨true,fun a => (c / 2) * (if a then 1 else -s.val),?_,?_⟩
    · intro a
      cases a <;> simp [hc,Units.ne_zero s.val]
    · funext a b
      cases a <;> cases b <;> simp [reflectedBinary,Holant.Marked.monomial]

def decompositionMatrix {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i : Fin D.count) : Holant.Marked.Mat :=
  fun a b => D.factor i (fun j => if j.val = 0 then a else b)

theorem binary_decomposition_matching {n : ℕ}
    (D : TensorDecomposition AlgebraicComplex n) (htwo : ∀ i,D.arity i = 2)
    (hM : ∀ i,Holant.Marked.IsMonomial (decompositionMatrix D i)) :
    Holant.Certificates.MatchingContractionClosure.MatchingOrZero monomialGroup D.value := by
  classical
  let p := (decompositionPairing D htwo).ports
  let M : Holant.Certificates.MatchingContractionClosure.Presentation AlgebraicComplex (Fin n) := {
    edges := D.count
    ports := p
    matrix := decompositionMatrix D
    scalar := (D.scale : AlgebraicComplex) }
  refine Or.inr ⟨M,fun i => (safe_monomial_iff _).mpr (hM i),Units.ne_zero D.scale,?_⟩
  funext x
  unfold TensorDecomposition.value
  change (D.scale : AlgebraicComplex) * ∏ i,D.factor i (fun j => x (D.ports ⟨i,j⟩)) =
    (D.scale : AlgebraicComplex) * ∏ i,decompositionMatrix D i (x (p (i,false))) (x (p (i,true)))
  apply congrArg ((D.scale : AlgebraicComplex) * ·)
  apply Finset.prod_congr rfl
  intro i _
  apply congrArg (D.factor i)
  funext j
  have hj : j.val = 0 ∨ j.val = 1 := by
    have hv : j.val < 2 := lt_of_lt_of_eq j.isLt (htwo i)
    omega
  rcases hj with hj | hj
  · have he : j = Fin.cast (htwo i).symm 0 := Fin.ext hj
    subst j
    simp [p,decompositionPairing,finTwoEquiv]
    rfl
  · have he : j = Fin.cast (htwo i).symm 1 := Fin.ext hj
    subst j
    simp [p,decompositionPairing,finTwoEquiv]
    rfl

theorem matching_scale {ι : Type*} {f : Tensor AlgebraicComplex ι}
    (hf : Holant.Certificates.MatchingContractionClosure.MatchingOrZero monomialGroup f)
    (c : AlgebraicComplex) :
    Holant.Certificates.MatchingContractionClosure.MatchingOrZero monomialGroup (c • f) := by
  classical
  by_cases hc : c = 0
  · subst c
    exact Or.inl (by simp)
  rcases hf with rfl | ⟨M,hM,hcM,rfl⟩
  · exact Or.inl (by simp)
  let R := {M with scalar := c * M.scalar}
  refine Or.inr ⟨R,hM,mul_ne_zero hc hcM,?_⟩
  funext x
  simp [R,Holant.Certificates.MatchingContractionClosure.Presentation.tensor,
    Holant.Certificates.MatchingContractionClosure.productValue,mul_assoc]

theorem minimum_card_walsh_matching {F : SignatureFamily AlgebraicComplex}
    (M : BinaryMenu F) (L : Language) (heven : ∀ f ∈ L.family,Even f.1)
    (hsafe : AllBinariesSafe L.family) {N n : ℕ}
    (hG : actualClasses L.family = dihedralPhaseClasses N) (hmin : LeastPrimeArity L.family n)
    (f : AnySignature AlgebraicComplex) (hf : f.1 = n) (hprocessed : M.Processed f L)
    (k : M.Choices f) (hcard : 0 < (M.produced f k).1 ∧ (M.produced f k).2 ≠ 0) :
    Holant.Certificates.MatchingContractionClosure.MatchingOrZero monomialGroup
      (walshCoordinates (M.produced f k).2) := by
  let Q := selectedDecomposition (M.produced f k) hcard
  have hQ := selectedDecomposition_spec (M.produced f k) hcard
  have hc (i : Fin Q.count) : (⟨Q.arity i,Q.factor i⟩ : AnySignature AlgebraicComplex) ∈ M.children f := by
    apply Set.mem_iUnion.mpr
    refine ⟨k,?_⟩
    rw [selectedFactors,dif_pos hcard]
    exact ⟨i,rfl⟩
  have hmem := fun i => hprocessed.2.1 (hc i)
  have htwo : ∀ i,Q.arity i = 2 := fun i =>
    selected_card_factors_binary M L heven hmin f hf hprocessed (hc i)
  have hp := binary_decomposition_matching (Q.mapAction walshInv) htwo (fun i => by
    have hh := normalized_walsh_monomial hG hsafe (Q.factor i) (htwo i)
      (networkRealizable_of_mem (hmem i)) (hQ.2.2 i).1
    change Holant.Marked.IsMonomial (fun a b =>
      (Signature.coordinateAction (fun _ => walshInv) (Q.factor i))
        (fun j => if j.val = 0 then a else b))
    rw [← walshCoordinates_eq_coordinateAction]
    exact hh)
  have he := (TensorDecomposition.value_mapAction Q walshInv).trans
    (walshCoordinates_eq_coordinateAction Q.value).symm
  rw [he,hQ.1] at hp
  exact hp

variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]

/-- Every literal analytic xor card has the complete monomial coefficients
of its actual retained binary decomposition, including the zero branch. -/
theorem minimum_xorCard_matching (C : XorCards F N) (L : Language)
    (heven : ∀ f ∈ L.family,Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hG : actualClasses L.family = dihedralPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n)
    (hprocessed : (xorMenu C).Processed ⟨n,f⟩ L)
    (a b : Fin n) (hab : a ≠ b) (u v : Bool) (s : rootsOfUnity N AlgebraicComplex) :
    Holant.Certificates.MatchingContractionClosure.MatchingOrZero monomialGroup
      (Tensor.reindex (Fintype.equivFin (EndpointSelfLoop.Remaining a b))
        (card (xorKernel u v s.val) a b hab (walshCoordinates f))) := by
  classical
  let k := xorChoice C f a b hab u v s
  let g := (xorMenu C).produced ⟨n,f⟩ k
  have hw := xor_produced_walsh C f a b hab u v s
  change walshCoordinates g.2 = _ at hw
  by_cases hn : g.2 = 0
  · apply Or.inl
    rw [hn,walsh_zero] at hw
    funext x
    exact (mul_eq_zero.mp (congrFun hw x).symm).resolve_left (C.scale_ne_zero u v s)
  have hp : 0 < g.1 := by
    have ha := (xorMenu C).produced_arity ⟨n,f⟩ k
    have h3 := hmin.ge_three
    change g.1 + 2 = n at ha
    omega
  have hm := minimum_card_walsh_matching (xorMenu C) L heven hsafe hG hmin
    ⟨n,f⟩ rfl hprocessed k ⟨hp,hn⟩
  rw [hw] at hm
  have hh := matching_scale hm (C.scale u v s)⁻¹
  rw [smul_smul,inv_mul_cancel₀ (C.scale_ne_zero u v s),one_smul] at hh
  exact hh

end
end Paper2.HeightOne.Dihedral.HighArity
