import Paper2.HeightOne.Dihedral.SixPortPorts

/-! The complete signed six-port algebraic base case, with all support and
coefficient conclusions proved from the literal three-phase xor cards. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Dihedral
noncomputable section
open Cyclic Tractable EndpointSelfLoop PhaseCards SixPortSupport SixPortPencils
local instance {ι : Type} : DecidableEq ι := Classical.decEq ι

lemma ordered_three_phase_union (f : Signature AlgebraicComplex 6) (hpar : HasParity f)
    (S : Finset AlgebraicComplex) (hS : S.card = 3) (hsne : ∀ s ∈ S, s ≠ 0)
    (hcards : ∀ p ξ s, s ∈ S → (pencilSupport (first f p ξ) (second f p ξ) s).card ≤ 4)
    (hcomp : ∀ p ξ s, s ∈ S → ∀ x ∈ pencilSupport (first f p ξ) (second f p ξ) s,
      complement x ∈ pencilSupport (first f p ξ) (second f p ξ) s)
    (p : Equiv.Perm (Fin 6)) (ξ : Bool) :
    (jointSupport (first f p ξ) (second f p ξ)).card ≤ 4 := by
  have hh := three_phase_union_card_le_four (Tensor.reindex p.symm f)
    (hasParity_reindex p.symm f hpar) S hS hsne
    (fun q η s hs => by simpa only [first_reindex,second_reindex] using hcards (q.trans p) η s hs)
    (fun q η s hs => by simpa only [first_reindex,second_reindex] using hcomp (q.trans p) η s hs) ξ
  simpa only [first_reindex,second_reindex,Equiv.refl_trans] using hh

theorem six_binary_decomposition_of_all_xor_cards (f : Signature AlgebraicComplex 6)
    (a : Fin 6 → Bool) (ha : f a ≠ 0) (s t u : AlgebraicComplex)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) (hu0 : u ≠ 0)
    (hcoset : ∀ i j (hij : i ≠ j) v w q, q = s ∨ q = t ∨ q = u →
      card (xorKernel v w q) i j hij f ≠ 0 →
        CosetMatchingSupport (card (xorKernel v w q) i j hij f))
    (hprod : ∀ i j (hij : i ≠ j) v w q, q = s ∨ q = t ∨ q = u →
      Product (Tensor.reindex (Fintype.equivFin (Remaining i j))
        (card (xorKernel v w q) i j hij f))) :
    ∃ D : TensorDecomposition AlgebraicComplex 6, D.value = f ∧ ∀ i, D.arity i = 2 := by
  classical
  let g := xorShift a f
  let S : Finset AlgebraicComplex := {s,t,u}
  have hS : S.card = 3 := by simp [S,hst,hsu,htu,Ne.symm hst,Ne.symm hsu,Ne.symm htu]
  have hSmem (q : AlgebraicComplex) : q ∈ S ↔ q = s ∨ q = t ∨ q = u := by simp [S]
  have hsne : ∀ q ∈ S,q ≠ 0 := by
    intro q hq
    rcases (hSmem q).mp hq with rfl | rfl | rfl <;> assumption
  have hc : ∀ i j (hij : i ≠ j) v w q, q ∈ S →
      card (xorKernel v w q) i j hij g ≠ 0 →
        CosetMatchingSupport (card (xorKernel v w q) i j hij g) := by
    intro i j hij v w q hq hn
    change card (xorKernel v w q) i j hij (xorShift a f) ≠ 0 at hn
    rw [card_xorShift] at hn
    have ho : card (xorKernel (a i ^^ v) (a j ^^ w) q) i j hij f ≠ 0 := by
      intro hz
      rw [hz] at hn
      exact hn rfl
    change CosetMatchingSupport (card (xorKernel v w q) i j hij (xorShift a f))
    rw [card_xorShift]
    exact (hcoset i j hij _ _ q ((hSmem q).mp hq) ho).xorShift _
  let phases : Fin 3 → AlgebraicComplex := ![s,t,u]
  have hphases : Function.Injective phases := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [phases]
  have hp : HasParity g := by
    apply hasParity_of_nonzero_three_phase_contractions (by simp) phases hphases g
    intro i j hij k hn
    have hq : phases k ∈ S := by fin_cases k <;> simp [phases,S]
    rw [← card_plus (phases k) i j hij g] at hn ⊢
    rw [← xorKernel_false_false] at hn ⊢
    exact (hc i j hij false false (phases k) hq hn).hasParity
  have hcards : ∀ p ξ q, q ∈ S →
      (pencilSupport (first g p ξ) (second g p ξ) q).card ≤ 4 := by
    intro p ξ q hq
    let H := card (xorKernel false ξ q) (p 0) (p 1) (pair_ports_ne p) g
    have he := ordered_pencil_card g p ξ q
    by_cases hn : H = 0
    · have hz : (fun r => first g p ξ r - q * second g p ξ r) = 0 := by
        rw [he]
        change Tensor.reindex (tailEquiv p).symm H = 0
        rw [hn]
        rfl
      have hz' : pencilSupport (first g p ξ) (second g p ξ) q = ∅ := by
        ext r
        have hh : first g p ξ r - q * second g p ξ r = 0 := congrFun hz r
        simp [hh]
      rw [hz']
      simp
    · have hh := (hc (p 0) (p 1) (pair_ports_ne p) false ξ q hq hn).card
      have hrem : Fintype.card (Remaining (p 0) (p 1)) = 4 := by
        have hh := remaining_card (p 0) (p 1) (pair_ports_ne p)
        simp only [Fintype.card_fin] at hh
        omega
      have hh' : (Cyclic.support H).card = 4 := by simpa [hrem,H] using hh
      have hsupport : pencilSupport (first g p ξ) (second g p ξ) q =
          Cyclic.support (fun r => first g p ξ r - q * second g p ξ r) := by
        ext r
        simp [pencilSupport,Cyclic.support]
      rw [hsupport]
      rw [he,support_reindex_card]
      exact hh'.le
  have hcomp : ∀ p ξ q, q ∈ S → ∀ r ∈ pencilSupport (first g p ξ) (second g p ξ) q,
      complement r ∈ pencilSupport (first g p ξ) (second g p ξ) q := by
    intro p ξ q hq r hr
    let H := card (xorKernel false ξ q) (p 0) (p 1) (pair_ports_ne p) g
    have he := ordered_pencil_card g p ξ q
    have hr' : H (fun k => r ((tailEquiv p).symm k)) ≠ 0 := by
      rw [mem_pencilSupport] at hr
      have hrr := congrFun he r
      change first g p ξ r - q * second g p ξ r = H (fun k => r ((tailEquiv p).symm k)) at hrr
      rwa [hrr] at hr
    have hn : H ≠ 0 := by intro hz; exact hr' (congrFun hz _)
    have hh := (hc (p 0) (p 1) (pair_ports_ne p) false ξ q hq hn).complement _ hr'
    rw [mem_pencilSupport]
    change (fun x => first g p ξ x - q * second g p ξ x) (complement r) ≠ 0
    rw [he]
    exact hh
  have hbound : ∀ p ξ, (jointSupport (first g p ξ) (second g p ξ)).card ≤ 4 :=
    ordered_three_phase_union g hp S hS hsne hcards hcomp
  have hmatch : ∀ i j (hij : i ≠ j), ∀ q, q = s ∨ q = t ∨ q = u →
      plusContraction i j hij q g ≠ 0 → EqualityMatchingSupport (plusContraction i j hij q g) := by
    intro i j hij q hq hn
    let p := pairPerm i j
    have hU : (jointSupport
        (fun x => g (extendBits i j hij x false false))
        (fun x => g (extendBits i j hij x true true))).card ≤ 4 := by
      have hh := hbound p false
      have hp0 : p 0 = i := pairPerm_zero i j hij
      have hp1 : p 1 = j := pairPerm_one i j
      rwa [equal_joint_card_as g p i j hij hp0 hp1] at hh
    have hrem : Fintype.card (Remaining i j) = 4 := by
      have hh := remaining_card i j hij
      simp only [Fintype.card_fin] at hh
      omega
    have hco : CosetMatchingSupport (plusContraction i j hij q g) := by
      rw [← card_plus q i j hij g,← xorKernel_false_false] at hn ⊢
      exact hc i j hij false false q ((hSmem q).mpr hq) hn
    have h0 : g (extendBits i j hij (fun _ => false) false false) ≠ 0 := by
      rw [extendBits_origin_false]
      change xorShift a f (fun _ => false) ≠ 0
      rwa [xorShift_origin]
    have hplus : plusContraction i j hij q g =
        (fun x => g (extendBits i j hij x false false) - q * g (extendBits i j hij x true true)) := by
      funext x
      exact plusContraction_apply i j hij q g x
    have hh := matching_pencil_of_union_bound
      (fun x => g (extendBits i j hij x false false))
      (fun x => g (extendBits i j hij x true true)) q (Or.inl h0)
      (by simpa [hrem] using hU) (by rwa [← hplus])
    rwa [← hplus] at hh
  apply six_binary_decomposition_of_shifted_cards f a ha s t u hst hsu htu hmatch
  intro i j hij q hq
  rw [plusContraction_xorShift,reindex_xorShift]
  exact product_xorShift (hprod i j hij (a i) (a j) q hq) _

end
end Paper2.HeightOne.Dihedral

