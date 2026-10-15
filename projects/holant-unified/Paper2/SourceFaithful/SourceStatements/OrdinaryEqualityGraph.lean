import Paper2.RelativeEO.GeneralizedEqualityGadget
import Paper2.DegreeCSP.Model
import Paper2.Paper1ProvedOddUnaryEquality
import Holant.OrdinaryNetwork

/-! Two copies of an ordinary higher equality produce equality four.  All
other corresponding ports are joined by actual identity wires.  The single
shared internal bit fixes the orientation, so no factor two is discarded. -/
namespace Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityGraph
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO EndpointSelfLoop
open scoped BigOperators Classical
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {d : ℕ}

private theorem finite_denote_equality {K V E : Type} [Fintype V] [Fintype E]
    [CommSemiring K] {n : ℕ} (N : FiniteNetwork K V E n)
    (hI : ∀ e, N.edge e = Signature.equality) (x : Fin n → Bool) :
    N.denote x = ∑ z : E → Bool,
      ∏ v, N.vertex v (fun i => Sum.elim x (fun q : E × Bool => z q.1)
        (N.ports ⟨v,i⟩)) := by
  classical
  unfold FiniteNetwork.denote
  rw [← (FiniteNetwork.edgeAssignmentEquiv E).symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  simp only [FiniteNetwork.edgeAssignmentEquiv,Equiv.coe_fn_symm_mk,hI,
    Bool.false_eq_true,↓reduceIte]
  have hp (b : E → Bool) :
      (∏ e,Signature.equality (K := K) (a e) (b e)) = if b = a then 1 else 0 := by
    simp only [Signature.equality,Fintype.prod_boole]
    simp only [show (∀ e,a e = b e) ↔ b = a by exact ⟨fun h => (funext h).symm,
      fun h e => congrFun h.symm e⟩]
  simp only [hp,mul_ite,mul_one,mul_zero]
  simp

def finite (i j : Fin d) (hij : i ≠ j) :
    FiniteNetwork AlgebraicComplex Bool (Remaining i j) 4 :=
  { gramFinite i j hij (DegreeCSP.equality (K := AlgebraicComplex) d) with
    edge := fun _ => Signature.equality }

theorem finite_denote (hd : 3 ≤ d) (i j : Fin d) (hij : i ≠ j) :
    (finite i j hij).toNetwork.denote = DegreeCSP.equality (K := AlgebraicComplex) 4 := by
  classical
  have hcard := remaining_card i j hij
  have hrem : 0 < Fintype.card (Remaining i j) := by
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨k⟩ := Fintype.card_pos_iff.mp hrem
  have hne : (fun _ : Remaining i j => false) ≠ (fun _ => true) := by
    intro h
    exact Bool.false_ne_true (congrFun h k)
  funext x
  rw [FiniteNetwork.denote_toNetwork,finite_denote_equality _ (fun _ => rfl)]
  have ha (z : Remaining i j → Bool) (v : Bool) :
      (fun p => Sum.elim x (fun q : Remaining i j × Bool => z q.1)
        (gramPorts i j hij ⟨v,p⟩)) =
      fillPair i j hij (x (quadPortEquiv (v,false)))
        (x (quadPortEquiv (v,true))) z := by
    funext p
    change Sum.elim x (fun q : Remaining i j × Bool => z q.1)
      (match splitPorts i j hij p with
        | .inl r => .inr (r,v)
        | .inr b => .inl (quadPortEquiv (v,b))) = _
    unfold fillPair
    cases splitPorts i j hij p with
    | inl r => rfl
    | inr b => cases b <;> rfl
  change (∑ z : Remaining i j → Bool,
    ∏ v : Bool,DegreeCSP.equality (K := AlgebraicComplex) d
      (fun p => Sum.elim x (fun q : Remaining i j × Bool => z q.1)
        (gramPorts i j hij ⟨v,p⟩))) = _
  simp_rw [ha]
  simp only [Fintype.prod_bool,DegreeCSP.equality_eq,fillPair_constant_iff]
  have hx0 : x = (fun _ => false) ↔
      x 0 = false ∧ x 1 = false ∧ x 2 = false ∧ x 3 = false := by
    constructor
    · rintro rfl; simp
    · rintro ⟨h0,h1,h2,h3⟩; funext t; fin_cases t <;> assumption
  have hx1 : x = (fun _ => true) ↔
      x 0 = true ∧ x 1 = true ∧ x 2 = true ∧ x 3 = true := by
    constructor
    · rintro rfl; simp
    · rintro ⟨h0,h1,h2,h3⟩; funext t; fin_cases t <;> assumption
  simp only [hx0,hx1]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [quadPortEquiv,h0,h1,h2,h3,hne,Ne.symm hne]

def imported {n : ℕ} (N : Network AlgebraicComplex n) : Holant.Network AlgebraicComplex n :=
  ⟨⟨N.shape.vertices,N.shape.arity,N.shape.edges,N.shape.ports⟩,N.vertex,N.edge⟩

/-- An actual ordinary graph using only two original equality vertices. -/
theorem equality_four_realized (L : Language) (hd : 3 ≤ d)
    (heq : (⟨d,DegreeCSP.equality (K := AlgebraicComplex) d⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ N : Holant.Network AlgebraicComplex 4,
      (∀ v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex) ∈ L.family) ∧
      (∀ e,N.edge e = Holant.Signature.equality) ∧
      N.denote = Holant.EightVertex.ProductAnchor.equalityFour := by
  let i : Fin d := ⟨0,by omega⟩
  let j : Fin d := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have := congrArg Fin.val h; dsimp [i,j] at this; omega
  refine ⟨imported (finite i j hij).toNetwork,(fun _ => heq),(fun _ => rfl),?_⟩
  change (finite i j hij).toNetwork.denote = _
  rw [finite_denote hd]
  rw [Paper2.Paper1Proved.OddUnary.equalityFour_points]
  funext x
  rw [DegreeCSP.equality_eq]
  rfl

end
end Paper2.SourceFaithful.SourceStatements.OrdinaryEqualityGraph

