import Paper2.TransversalCube.Graph
import Paper2.TransversalCube.Obstruction
import Paper2.Paper1Accepted.Terminals

/-! Source lemma `lem:hc-transversal-cube-terminal`: an arbitrary weighted
matching-product central layer gives a two-copy, all-native-X quaternary with
all six central entries nonzero. The graph and literal EOTract obstruction are
proved without any complexity premise. Only the separately named Paper 1 EO
interface is used for the final singleton-language hardness corollary. -/
namespace Paper2.TransversalCube
open scoped BigOperators
open Tractable ExactInput
noncomputable section

variable {K : Type*} [CommRing K] [IsDomain K] {n : ℕ}

/-- The exact mountain expression in the original ordered ports. -/
def sourceMountain (P : WeightedMatching.Pairing n) (a b c : K)
    (p q : Fin P.count → K) : Signature K n := fun x =>
  (if x = (fun _ => false) then a else 0) +
  (if x = (fun _ => true) then b else 0) + WeightedMatching.product P p q c x

/-- A source-exact graph witness. No relabeled copy is inserted into F: both
vertices carry the supplied original mountain, with its original port order. -/
theorem exists_native_gadget (P : WeightedMatching.Pairing n) (hd : 3 ≤ P.count)
    (a b c : K) (p q : Fin P.count → K) (hab : a*b ≠ 0)
    (hcoeff : c * ∏ j, p j * q j ≠ 0) (F : SignatureFamily K)
    (hM : (⟨n,sourceMountain P a b c p q⟩ : AnySignature K) ∈ F) :
    ∃ N : Network K 4, N.Uses F ∧ N.NativeX ∧ N.shape.vertices = 2 ∧
      N.shape.edges = 2*(P.count-1) ∧
      (∀ x, N.denote x ≠ 0 ↔ weight x = 2) ∧
      N.denote ![false,false,true,true] = a*b ∧
      N.denote ![true,true,false,false] = a*b ∧
      ¬ WeightedMatching.IsProduct N.denote := by
  rcases P with ⟨d,e⟩
  cases d with
  | zero => simp at hd
  | succ m =>
    have hm : 2 ≤ m := by simpa using hd
    have he : sourceMountain ⟨m+1,e⟩ a b c p q = orderedMountain e a b c p q := by
      funext x; exact (orderedMountain_eq_source e a b c p q x).symm
    rw [he] at hM
    let N := network e (orderedMountain e a b c p q)
    have hN : N.denote = contract a b c p q := network_denote e a b c p q
    have ha := left_ne_zero_of_mul hab
    have hb := right_ne_zero_of_mul hab
    have hs : ∀ x, N.denote x ≠ 0 ↔ weight x = 2 := by
      intro x; rw [hN]; exact contract_weight_two hm a b c p q ha hb hcoeff x
    refine ⟨N,network_uses e _ F hM,network_nativeX e _,network_vertices e _,?_,hs,?_,?_,
      six_not_isProduct N.denote hs⟩
    · simpa using network_edges e (orderedMountain e a b c p q)
    · rw [hN]; exact contract_endpoint hm a b c p q ha hb hcoeff false
    · rw [hN]; exact contract_endpoint hm a b c p q ha hb hcoeff true

/-- Literal six-entry equation WT.18a for the actual network denotation. -/
theorem exists_native_gadget_WT18a (P : WeightedMatching.Pairing n) (hd : 3 ≤ P.count)
    (a b c : K) (p q : Fin P.count → K) (hab : a*b ≠ 0)
    (hcoeff : c * ∏ j, p j * q j ≠ 0) (F : SignatureFamily K)
    (hM : (⟨n,sourceMountain P a b c p q⟩ : AnySignature K) ∈ F) :
    ∃ N : Network K 4, ∃ c₁ c₂ c₃ c₄ : K,
      N.Uses F ∧ N.NativeX ∧
      ![N.denote ![false,false,true,true], N.denote ![false,true,false,true],
        N.denote ![false,true,true,false], N.denote ![true,false,false,true],
        N.denote ![true,false,true,false], N.denote ![true,true,false,false]] =
        ![a*b,c₁,c₂,c₃,c₄,a*b] ∧
      c₁*c₂*c₃*c₄ ≠ 0 ∧ (∀ x, N.denote x ≠ 0 ↔ weight x = 2) := by
  obtain ⟨N,hU,hX,_,_,hs,h0,h1,_⟩ := exists_native_gadget P hd a b c p q hab hcoeff F hM
  refine ⟨N,N.denote ![false,true,false,true],N.denote ![false,true,true,false],
    N.denote ![true,false,false,true],N.denote ![true,false,true,false],hU,hX,?_,?_,hs⟩
  · rw [h0,h1]
  · repeat apply mul_ne_zero
    all_goals exact (hs _).2 (by decide +kernel)

/-- Structural conclusion of WT.18a, including the literal family-wide
sign obstruction in EOTract. This theorem assumes no Paper 1 interface. -/
theorem matching_mountain_terminal (P : WeightedMatching.Pairing n) (hd : 3 ≤ P.count)
    (a b c : AlgebraicComplex) (p q : Fin P.count → AlgebraicComplex) (hab : a*b ≠ 0)
    (hcoeff : c * ∏ j, p j * q j ≠ 0) (F : SignatureFamily AlgebraicComplex)
    (hM : (⟨n,sourceMountain P a b c p q⟩ : AnySignature AlgebraicComplex) ∈ F) :
    ∃ N : Network AlgebraicComplex 4, N.Uses F ∧ N.NativeX ∧
      N.shape.vertices = 2 ∧ N.shape.edges = 2*(P.count-1) ∧
      (∀ x, N.denote x ≠ 0 ↔ weight x = 2) ∧
      N.denote ![false,false,true,true] = a*b ∧
      N.denote ![true,true,false,false] = a*b ∧
      ¬ WeightedMatching.IsProduct N.denote ∧
      IsEO ⟨4,N.denote⟩ ∧ ¬ EOTract {⟨4,N.denote⟩} := by
  obtain ⟨N,hU,hX,hv,he,hs,h0,h1,hB⟩ := exists_native_gadget P hd a b c p q hab hcoeff F hM
  exact ⟨N,hU,hX,hv,he,hs,h0,h1,hB,six_isEO N.denote hs,six_not_eoTract N.denote hs⟩

/-- The separately accepted weighted-EO dichotomy gives an actual singleton
root-coded hard language, not a hardness label on an arbitrary predicate. -/
theorem six_singleton_hard (EO : Paper1EOAccepted) (f : Signature AlgebraicComplex 4)
    (hf : ∀ x, f x ≠ 0 ↔ weight x = 2) :
    ∃ H : Language, H.family = {⟨4,f⟩} ∧ Problem.SharpPHard .nativeX H := by
  obtain ⟨H,hH⟩ := Language.coverage_family ({⟨4,f⟩} : SignatureFamily AlgebraicComplex)
    (Set.finite_singleton _)
  refine ⟨H,hH,(EO.eo_2_16 H ?_ ?_).2 ?_⟩
  · intro g hg
    rw [hH, Set.mem_singleton_iff] at hg
    subst g
    refine ⟨by change 0 < 4; decide, ?_⟩
    intro hz
    have hn := (hf ![false, false, true, true]).2 (by decide +kernel)
    exact hn (congrFun hz _)
  · intro g hg
    rw [hH,Set.mem_singleton_iff] at hg
    subst g
    exact six_isEO f hf
  · rw [hH]
    exact six_not_eoTract f hf

/-- Literal augmentation and the singleton-to-ambient reduction are valid
without a bound assumption. Transporting actual hardness additionally needs a
bounded-answer convention for the ambient language; that obligation is explicit. -/
theorem matching_mountain_hard_of_bounded
    (DG : Paper1DirectGadgetAccepted) (R : Paper1RestrictionAccepted) (EO : Paper1EOAccepted)
    (L : Language) (P : WeightedMatching.Pairing n) (hd : 3 ≤ P.count)
    (a b c : AlgebraicComplex) (p q : Fin P.count → AlgebraicComplex) (hab : a*b ≠ 0)
    (hcoeff : c * ∏ j, p j * q j ≠ 0)
    (hM : (⟨n,sourceMountain P a b c p q⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hbounded : Nonempty (Problem.BoundedAnswers .nativeX L)) :
    Problem.SharpPHard .nativeX L := by
  obtain ⟨N,hU,hX,_,_,hs,_,_,_⟩ := exists_native_gadget P hd a b c p q hab hcoeff L.family hM
  have hreal : NativeNetworkRealizesUpTo L.family N.denote :=
    ⟨N,hU,hX,1,one_ne_zero,by simp⟩
  obtain ⟨A,hA,hAL⟩ := DG.adjoin L N.denote hreal
  obtain ⟨H,hH,hHard⟩ := six_singleton_hard EO N.denote hs
  have hHA : Problem.Reduces .nativeX H A := R.restriction_2_5 H A (by
    rw [hH,hA]
    exact Set.singleton_subset_iff.mpr (Set.mem_insert _ _))
  exact hHard.transport (hHA.trans hAL) hbounded

end
end Paper2.TransversalCube
