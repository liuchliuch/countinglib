import Paper2.Mountain
import Paper2.NetworkContraction
import Paper2.NetworkGluing.Finite

/-!
# Concrete native-X networks for Section 4's endpoint-pair constructions

The table operations in `MountainConstruction.PairGadget` are related here to
actual incidence-bijection networks. Every internal X edge is retained, and
its two endpoint bits are summed independently in `Network.denote`.
-/

set_option backward.isDefEq.respectTransparency false

namespace Paper2

open scoped BigOperators Classical

namespace FiniteNetwork

variable {K V E : Type*} {n : ℕ}

/-- Split all independent edge-end assignments into the two oriented words. -/
def edgeAssignmentEquiv (E : Type*) :
    ((E × Bool) → Bool) ≃ ((E → Bool) × (E → Bool)) where
  toFun z := (fun e => z (e, false), fun e => z (e, true))
  invFun p := fun q => if q.2 then p.2 q.1 else p.1 q.1
  left_inv := by intro z; funext q; rcases q with ⟨e, b⟩; cases b <;> rfl
  right_inv := by intro p; rfl

theorem prod_disequality [Fintype E] [CommSemiring K] (a b : E → Bool) :
    (∏ e, Signature.disequality (K := K) (a e) (b e)) =
      if b = (fun e => !(a e)) then 1 else 0 := by
  classical
  have h : (∀ e, a e ≠ b e) ↔ b = (fun e => !(a e)) := by
    constructor
    · intro h
      funext e
      have he := h e
      cases ha : a e <;> cases hb : b e <;> simp_all
    · rintro rfl e
      cases ha : a e <;> simp [ha]
  simp only [Signature.disequality, Fintype.prod_boole, h]

/-- Exact elimination of the redundant edge-end word for native-X networks.
This is derived from the original sum with an X factor for every edge. -/
theorem denote_nativeX [Fintype V] [Fintype E] [CommSemiring K]
    (N : FiniteNetwork K V E n) (hX : ∀ e, N.edge e = Signature.disequality)
    (x : Fin n → Bool) :
    N.denote x = ∑ z : E → Bool,
      ∏ v, N.vertex v (fun i => Sum.elim x
        (fun q : E × Bool => if q.2 then !(z q.1) else z q.1) (N.ports ⟨v, i⟩)) := by
  classical
  unfold denote
  rw [← (edgeAssignmentEquiv E).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [edgeAssignmentEquiv, Equiv.coe_fn_symm_mk, hX]
  simp only [prod_disequality, mul_ite, mul_one, mul_zero]
  simp

end FiniteNetwork

namespace MountainConstruction

variable {K : Type*} {d : ℕ}

/-- Incidences for two vertices: each first block is external, each second
block is one oriented side of the matching internal X edges. -/
def pairPorts (d : ℕ) :
    (Σ _ : Bool, Fin d ⊕ Fin d) ≃ ((Fin d ⊕ Fin d) ⊕ (Fin d × Bool)) where
  toFun
    | ⟨false, .inl i⟩ => .inl (.inl i)
    | ⟨true, .inl i⟩ => .inl (.inr i)
    | ⟨b, .inr i⟩ => .inr (i, b)
  invFun
    | .inl (.inl i) => ⟨false, .inl i⟩
    | .inl (.inr i) => ⟨true, .inl i⟩
    | .inr (i, b) => ⟨b, .inr i⟩
  left_inv := by rintro ⟨b, i | i⟩ <;> cases b <;> rfl
  right_inv := by rintro ((i | i) | ⟨i, b⟩); rfl; rfl; cases b <;> rfl

/-- Two genuine supplied vertices, with permutations in their incidences,
not in the supplied tables, and exactly `d` internal native-X edges. -/
noncomputable def joinXFinite [CommSemiring K]
    (P N : Tensor K (Fin d ⊕ Fin d)) (eP eN : Equiv.Perm (Fin d ⊕ Fin d)) :
    FiniteNetwork K Bool (Fin d) (2 * d) where
  arity := fun _ => 2 * d
  ports := (Equiv.sigmaCongrRight (fun b : Bool =>
    (blockEquiv d).symm.trans (if b then eN else eP))).trans
      ((pairPorts d).trans (Equiv.sumCongr (blockEquiv d) (Equiv.refl _)))
  vertex := fun b => Tensor.reindex (blockEquiv d) (if b then N else P)
  edge := fun _ => Signature.disequality

/-- The two-vertex network's denotation is precisely the connector table. -/
theorem denote_joinXFinite [CommSemiring K]
    (P N : Tensor K (Fin d ⊕ Fin d)) (eP eN : Equiv.Perm (Fin d ⊕ Fin d)) :
    (joinXFinite P N eP eN).denote =
      Tensor.reindex (blockEquiv d) (joinX (Tensor.reindex eP P) (Tensor.reindex eN N)) := by
  classical
  funext x
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  simp only [Tensor.reindex, joinX]
  refine Finset.sum_congr (by ext; simp) ?_
  intro z _
  rw [Fintype.prod_bool]
  have hP : (fun i => Sum.elim x
      (fun q : Fin d × Bool => if q.2 then !(z q.1) else z q.1)
      ((joinXFinite P N eP eN).ports ⟨false, (blockEquiv d) i⟩)) =
      (fun i => Sum.elim (fun j => x ((blockEquiv d) (.inl j))) z (eP i)) := by
    funext i
    simp only [joinXFinite, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
      Equiv.symm_apply_apply, Bool.false_eq_true, ite_false]
    cases eP i <;> rfl
  have hN : (fun i => Sum.elim x
      (fun q : Fin d × Bool => if q.2 then !(z q.1) else z q.1)
      ((joinXFinite P N eP eN).ports ⟨true, (blockEquiv d) i⟩)) =
      (fun i => Sum.elim (fun j => x ((blockEquiv d) (.inr j)))
        (fun j => !(z j)) (eN i)) := by
    funext i
    simp only [joinXFinite, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
      Equiv.symm_apply_apply, ite_true]
    cases eN i <;> rfl
  change N (fun i => Sum.elim x
      (fun q : Fin d × Bool => if q.2 then !(z q.1) else z q.1)
      ((joinXFinite P N eP eN).ports ⟨true, (blockEquiv d) i⟩)) *
    P (fun i => Sum.elim x
      (fun q : Fin d × Bool => if q.2 then !(z q.1) else z q.1)
      ((joinXFinite P N eP eN).ports ⟨false, (blockEquiv d) i⟩)) = _
  rw [hP, hN]
  exact mul_comm _ _

/-- Three supplied vertices and `2*d` matching edges, with the middle table's
two blocks facing the last blocks of the two copies. -/
def triplePorts (d : ℕ) :
    (Σ _ : Option Bool, Fin d ⊕ Fin d) ≃
      ((Fin d ⊕ Fin d) ⊕ ((Fin d ⊕ Fin d) × Bool)) where
  toFun
    | ⟨some false, .inl i⟩ => .inl (.inl i)
    | ⟨some true, .inl i⟩ => .inl (.inr i)
    | ⟨some false, .inr i⟩ => .inr (.inl i, false)
    | ⟨some true, .inr i⟩ => .inr (.inr i, false)
    | ⟨none, i⟩ => .inr (i, true)
  invFun
    | .inl (.inl i) => ⟨some false, .inl i⟩
    | .inl (.inr i) => ⟨some true, .inl i⟩
    | .inr (.inl i, false) => ⟨some false, .inr i⟩
    | .inr (.inr i, false) => ⟨some true, .inr i⟩
    | .inr (i, true) => ⟨none, i⟩
  left_inv := by rintro ⟨(_ | b), (i | i)⟩ <;> (try cases b) <;> rfl
  right_inv := by rintro ((i | i) | ⟨(i | i), b⟩) <;> (try cases b) <;> rfl

noncomputable def joinTwoCopiesXFinite [CommSemiring K]
    (P N : Tensor K (Fin d ⊕ Fin d)) (eP : Equiv.Perm (Fin d ⊕ Fin d)) :
    FiniteNetwork K (Option Bool) (Fin d ⊕ Fin d) (2 * d) where
  arity := fun _ => 2 * d
  ports := (Equiv.sigmaCongrRight (fun b : Option Bool =>
    (blockEquiv d).symm.trans (b.elim (Equiv.refl _) (fun _ => eP)))).trans
      ((triplePorts d).trans (Equiv.sumCongr (blockEquiv d) (Equiv.refl _)))
  vertex := fun b => Tensor.reindex (blockEquiv d) (b.elim N (fun _ => P))
  edge := fun _ => Signature.disequality

/-- Split an edge word on the two disjoint edge blocks. -/
def blockAssignmentEquiv (d : ℕ) :
    ((Fin d ⊕ Fin d) → Bool) ≃ ((Fin d → Bool) × (Fin d → Bool)) where
  toFun z := (fun i => z (.inl i), fun i => z (.inr i))
  invFun p := Sum.elim p.1 p.2
  left_inv := by intro z; funext i; cases i <;> rfl
  right_inv := by intro p; rfl

/-- Exact network realization of the three-signature finite sum. -/
theorem denote_joinTwoCopiesXFinite [CommSemiring K]
    (P N : Tensor K (Fin d ⊕ Fin d)) (eP : Equiv.Perm (Fin d ⊕ Fin d)) :
    (joinTwoCopiesXFinite P N eP).denote =
      Tensor.reindex (blockEquiv d) (joinTwoCopiesX (Tensor.reindex eP P) N) := by
  classical
  letI : DecidableEq (Fin d ⊕ Fin d) := Classical.decEq _
  funext x
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  rw [← (blockAssignmentEquiv d).symm.sum_comp]
  simp only [Fintype.sum_prod_type, Tensor.reindex, joinTwoCopiesX]
  refine Finset.sum_congr (by ext; simp) ?_
  intro z _
  refine Finset.sum_congr (by ext; simp) ?_
  intro w _
  rw [Fintype.prod_option, Fintype.prod_bool]
  let a : (Fin d ⊕ Fin d) × Bool → Bool :=
    fun q => if q.2 then !(Sum.elim z w q.1) else Sum.elim z w q.1
  have hP₀ : (fun i => Sum.elim x a
      ((joinTwoCopiesXFinite P N eP).ports ⟨some false, (blockEquiv d) i⟩)) =
      (fun i => Sum.elim (fun j => x ((blockEquiv d) (.inl j))) z (eP i)) := by
    funext i
    simp only [joinTwoCopiesXFinite, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
      Equiv.symm_apply_apply, Option.elim_some]
    cases eP i <;> rfl
  have hP₁ : (fun i => Sum.elim x a
      ((joinTwoCopiesXFinite P N eP).ports ⟨some true, (blockEquiv d) i⟩)) =
      (fun i => Sum.elim (fun j => x ((blockEquiv d) (.inr j))) w (eP i)) := by
    funext i
    simp only [joinTwoCopiesXFinite, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
      Equiv.symm_apply_apply, Option.elim_some]
    cases eP i <;> rfl
  have hN : (fun i => Sum.elim x a
      ((joinTwoCopiesXFinite P N eP).ports ⟨none, (blockEquiv d) i⟩)) =
      Sum.elim (fun j => !(z j)) (fun j => !(w j)) := by
    funext i
    simp only [joinTwoCopiesXFinite, Equiv.trans_apply, Equiv.sigmaCongrRight_apply,
      Equiv.symm_apply_apply, Option.elim_none, Equiv.refl_apply]
    cases i <;> rfl
  change N (fun i => Sum.elim x a
      ((joinTwoCopiesXFinite P N eP).ports ⟨none, (blockEquiv d) i⟩)) *
    (P (fun i => Sum.elim x a
      ((joinTwoCopiesXFinite P N eP).ports ⟨some true, (blockEquiv d) i⟩)) *
      P (fun i => Sum.elim x a
        ((joinTwoCopiesXFinite P N eP).ports ⟨some false, (blockEquiv d) i⟩))) = _
  rw [hP₀, hP₁, hN]
  ac_rfl

/-- Exact supplied vertex tables: arities and coefficient functions are both
recorded in the dependent pair, so no rescaling or port permutation is hidden. -/
def UsesPair (P N : Tensor K (Fin d ⊕ Fin d)) {n : ℕ} (G : Network K n) : Prop :=
  ∀ v, (⟨G.shape.arity v, G.vertex v⟩ : Σ r, Signature K r) =
      ⟨2 * d, Tensor.reindex (blockEquiv d) P⟩ ∨
    (⟨G.shape.arity v, G.vertex v⟩ : Σ r, Signature K r) =
      ⟨2 * d, Tensor.reindex (blockEquiv d) N⟩

/-- Every table in the explicit endpoint-pair menu is the exact denotation
of an actual finite native-X network using only the two original tables. -/
theorem PairGadget.realized [CommSemiring K]
    {P N M : Tensor K (Fin d ⊕ Fin d)} (h : PairGadget P N M) :
    ∃ G : Network K (2 * d), UsesPair P N G ∧
      (∀ e, G.edge e = Signature.disequality) ∧
      G.denote = Tensor.reindex (blockEquiv d) M := by
  classical
  cases h with
  | useLeft =>
    refine ⟨Network.corolla (Tensor.reindex (blockEquiv d) P), ?_, ?_,
      Network.denote_corolla _⟩
    · intro v
      exact Or.inl rfl
    · intro e
      exact Fin.elim0 e
  | useRight =>
    refine ⟨Network.corolla (Tensor.reindex (blockEquiv d) N), ?_, ?_,
      Network.denote_corolla _⟩
    · intro v
      exact Or.inr rfl
    · intro e
      exact Fin.elim0 e
  | join eP eN =>
    refine ⟨(joinXFinite P N eP eN).toNetwork, ?_, fun _ => rfl, ?_⟩
    · intro v
      change (⟨2 * d, Tensor.reindex (blockEquiv d)
          (if (Fintype.equivFin Bool).symm v then N else P)⟩ : Σ r, Signature K r) =
          ⟨2 * d, Tensor.reindex (blockEquiv d) P⟩ ∨
        (⟨2 * d, Tensor.reindex (blockEquiv d)
          (if (Fintype.equivFin Bool).symm v then N else P)⟩ : Σ r, Signature K r) =
          ⟨2 * d, Tensor.reindex (blockEquiv d) N⟩
      cases (Fintype.equivFin Bool).symm v <;> simp
    · rw [FiniteNetwork.denote_toNetwork, denote_joinXFinite]
  | doubleLeft eP =>
    refine ⟨(joinTwoCopiesXFinite P N eP).toNetwork, ?_, fun _ => rfl, ?_⟩
    · intro v
      change (⟨2 * d, Tensor.reindex (blockEquiv d)
          (((Fintype.equivFin (Option Bool)).symm v).elim N (fun _ => P))⟩ :
          Σ r, Signature K r) = _ ∨ _
      cases hb : (Fintype.equivFin (Option Bool)).symm v <;> simp [FiniteNetwork.toNetwork, joinTwoCopiesXFinite, hb]
    · rw [FiniteNetwork.denote_toNetwork, denote_joinTwoCopiesXFinite]
  | doubleRight eN =>
    refine ⟨(joinTwoCopiesXFinite N P eN).toNetwork, ?_, fun _ => rfl, ?_⟩
    · intro v
      change (⟨2 * d, Tensor.reindex (blockEquiv d)
          (((Fintype.equivFin (Option Bool)).symm v).elim P (fun _ => N))⟩ :
          Σ r, Signature K r) = _ ∨ _
      cases hb : (Fintype.equivFin (Option Bool)).symm v <;> simp [FiniteNetwork.toNetwork, joinTwoCopiesXFinite, hb]
    · rw [FiniteNetwork.denote_toNetwork, denote_joinTwoCopiesXFinite]

/-- Section 4's post-endpoint alternative, now with an actual graph witness
whose edges are native X and whose vertices are exactly the supplied P or N. -/
theorem nativeX_network_mountain_or_pure [CommSemiring K] [NoZeroDivisors K]
    {P N : Tensor K (Fin d ⊕ Fin d)} (hd : 0 < d)
    (hPone : P (fun _ => true) ≠ 0) (hNzero : N (fun _ => false) ≠ 0)
    (hPd : Tensor.HalfChargeDivisible P d) (hNd : Tensor.HalfChargeDivisible N d) :
    (∃ G : Network K (2 * d), UsesPair P N G ∧
      (∀ e, G.edge e = Signature.disequality) ∧ IsMountain G.denote) ∨
      (P = onePointMass (P (fun _ => true)) ∧
        N = zeroPointMass (N (fun _ => false))) := by
  rcases endpoint_pair_mountain_or_pure_of_divisible hd hPone hNzero hPd hNd with
    ⟨M, hM, hm⟩ | hpure
  · obtain ⟨G, hG, hX, he⟩ := hM.realized
    exact Or.inl ⟨G, hG, hX, he ▸ hm⟩
  · exact Or.inr hpure

end MountainConstruction
end Paper2
