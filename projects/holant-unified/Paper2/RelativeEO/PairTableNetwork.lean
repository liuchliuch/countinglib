import Paper2.RelativeEO.PairTable
import Paper2.RelativeEO.WeightedComplementaryExit

/-! Two actual copies of a pair-supported quaternary. Two native-X edges
implement H X Hᵀ on the compressed coefficient array. For ad=-bc the output
is a nonzero complementary quaternary, hence the already proved ambient exit. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open scoped BigOperators

@[simp] theorem pairTable_quad (g : Signature AlgebraicComplex 2) (a b c d : Bool) :
    pairTable g (quadWord a b c d) =
      if b = !a ∧ d = !c then g (binWord a c) else 0 := rfl

noncomputable def pairFinite (g : Signature AlgebraicComplex 2) :
    FiniteNetwork AlgebraicComplex Bool (Fin 2) 4 where
  arity _ := 4
  ports := weightedPorts
  vertex _ := pairTable g
  edge _ := Signature.disequality

noncomputable def pairNetwork (g : Signature AlgebraicComplex 2) : Network AlgebraicComplex 4 :=
  (pairFinite g).toNetwork

/-- No conjugation is used: the two copies contract by the native bilinear X. -/
theorem pairNetwork_denote (g : Signature AlgebraicComplex 2)
    (hneg : g (binWord false false) * g (binWord true true) +
      g (binWord false true) * g (binWord true false) = 0) :
    (pairNetwork g).denote = complementaryTable (quadWord false true true false)
      (2 * g (binWord false false) * g (binWord false true))
      (2 * g (binWord true false) * g (binWord true true)) := by
  classical
  letI : DecidableEq (Fin 2) := Classical.decEq (Fin 2)
  funext x
  rw [pairNetwork,FiniteNetwork.denote_toNetwork]
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  change (∑ z : Fin 2 → Bool, ∏ v : Bool,
    pairTable g (fun i => Sum.elim x
      (fun a : Fin 2 × Bool => if a.2 then !(z a.1) else z a.1) (weightedPorts ⟨v,i⟩))) = _
  rw [← pairAssignmentEquiv.symm.sum_comp,Fintype.sum_prod_type]
  simp only [Fintype.sum_bool,Fintype.prod_bool]
  change
    (pairTable g (quadWord (x 3) (x 1) false false) *
        pairTable g (quadWord (x 0) (x 2) true true) +
      pairTable g (quadWord (x 3) (x 1) false true) *
        pairTable g (quadWord (x 0) (x 2) true false)) +
    (pairTable g (quadWord (x 3) (x 1) true false) *
        pairTable g (quadWord (x 0) (x 2) false true) +
      pairTable g (quadWord (x 3) (x 1) true true) *
        pairTable g (quadWord (x 0) (x 2) false false)) = _
  have hcomp : (fun i => !(quadWord false true true false i)) = quadWord true false false true := by
    funext i; fin_cases i <;> rfl
  simp only [complementaryTable,hcomp,quadWord_eq_iff]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [pairTable_quad,h0,h1,h2,h3] <;> first | solve | ring | linear_combination hneg

/-- Substitute the original table with its explicit boundary permutation at
both vertices, so only original labels occur in the resulting actual graph. -/
theorem pairNetwork_realizable {F : SignatureFamily AlgebraicComplex}
    (f : Signature AlgebraicComplex 4) (e : Equiv.Perm (Fin 4))
    (g : Signature AlgebraicComplex 2) (he : Tensor.reindex e f = pairTable g)
    (hmem : (⟨4,f⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hneg : g (binWord false false) * g (binWord true true) +
      g (binWord false true) * g (binWord true false) = 0) :
    NativeNetworkRealizesUpTo F (complementaryTable (quadWord false true true false)
      (2 * g (binWord false false) * g (binWord false true))
      (2 * g (binWord true false) * g (binWord true true))) := by
  let R := (Network.corolla f).reindexBoundary e
  have hRU : R.Uses F := fun _ => hmem
  have hRX : R.NativeX := fun i => Fin.elim0 i
  have hRd : R.denote = pairTable g := by
    rw [Network.denote_reindexBoundary,Network.denote_corolla]
    exact he
  let G := pairNetwork g
  let replacements : (v : Fin G.shape.vertices) → Network AlgebraicComplex (G.shape.arity v) := fun _ => R
  have hGX : G.NativeX := fun _ => rfl
  refine ⟨G.substitute replacements,G.substitute_uses replacements (fun _ => hRU),
    G.substitute_nativeX replacements hGX (fun _ => hRX),1,one_ne_zero,?_⟩
  rw [G.denote_substitute replacements hGX (fun _ => hRX) (fun _ => hRd),pairNetwork_denote g hneg]
  simp

/-- A realized nonzero complementary quaternary closes the original ambient
language after a retained finite augmentation. -/
theorem realized_complementary_hard (G : Paper1DirectGadgetAccepted)
    (P : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (s : Fin 4 → Bool) (hs : weight s = 2)
    (p q : AlgebraicComplex) (hp : p ≠ 0) (hq : q ≠ 0)
    (hD : NativeNetworkRealizesUpTo L.family (complementaryTable s p q)) :
    SharpPHard .nativeX L := by
  have hscomp : s ≠ (fun i => !(s i)) := by
    intro he
    have hh := congrFun he 0
    exact Bool.not_ne_self (s 0) hh.symm
  have hnon : complementaryTable s p q ≠ 0 := by
    intro hz
    have hh := congrFun hz s
    simp [complementaryTable,hscomp,hp] at hh
  obtain ⟨M,hM,hML⟩ := G.adjoin L _ hD
  have hLM : L.family ⊆ M.family := by rw [hM]; exact Set.subset_insert _ _
  have hpreM : Preprocessed M.family := by
    intro t ht
    rw [hM] at ht
    rcases ht with rfl | ht
    · exact ⟨by change 0 < (4 : ℕ); decide,hnon⟩
    · exact hpre t ht
  have hbothM : BothChargeSigns M.family := by
    obtain ⟨⟨f,hf,x,hx,hn⟩,⟨g,hg,y,hy,hp⟩⟩ := hboth
    exact ⟨⟨f,hLM hf,x,hx,hn⟩,⟨g,hLM hg,y,hy,hp⟩⟩
  have hnotM : ¬ Tract (kImage M) := fun ht =>
    hnot (ht.mono_family (familyAction_mono sourceKBasis hLM))
  exact (complementary_hard G P F U M hpreM hbothM hnotM s hs p q hp hq
    (by rw [hM]; exact Set.mem_insert _ _)).transport_unconditional hML

end Paper2.RelativeEO
