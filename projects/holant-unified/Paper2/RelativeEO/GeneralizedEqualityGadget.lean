import Paper2.RelativeEO.GramNetwork
import Paper2.RelativeEO.MatchingComplementSix
import Paper2.RelativeEO.ARSMatching

/-! Two actual copies of an endpoint-only signature joined by every original
port except the two displayed external ports on each copy.  The existing Gram
network has no conjugate labels: it uses two copies of exactly the input and
only native X edges.  Its output is computed here without a central tensor. -/
namespace Paper2.RelativeEO
open Tractable ExactInput EndpointSelfLoop
open scoped BigOperators
noncomputable section
variable {n : ℕ}

def generalizedEquality (a b : AlgebraicComplex) : Signature AlgebraicComplex n := by
  classical
  exact fun x => (if x = (fun _ => false) then a else 0) +
    (if x = (fun _ => true) then b else 0)

theorem fillPair_constant_iff (i j : Fin n) (hij : i ≠ j) (u v t : Bool)
    (z : Remaining i j → Bool) :
    fillPair i j hij u v z = (fun _ => t) ↔
      u = t ∧ v = t ∧ z = (fun _ => t) := by
  constructor
  · intro h
    refine ⟨by simpa using congrFun h i,by simpa using congrFun h j,?_⟩
    funext k
    simpa using congrFun h k.val
  · rintro ⟨rfl,rfl,rfl⟩
    funext k
    unfold fillPair
    cases splitPorts i j hij k with
    | inl k => rfl
    | inr t => cases t <;> rfl

private theorem complement_constant_iff {ι : Type} (z : ι → Bool) (t : Bool) :
    (fun i => !(z i)) = (fun _ => t) ↔ z = (fun _ => !t) := by
  constructor
  · intro h
    funext i
    have hh := congrFun h i
    cases t <;> cases hz : z i <;> simp_all
  · rintro rfl
    funext i
    simp

/-- The exact four-port output, including its endpoint product scalar. -/
theorem generalizedEquality_gram_formula (hn : 3 ≤ n)
    (i j : Fin n) (hij : i ≠ j) (a b : AlgebraicComplex) :
    gramTable i j hij (generalizedEquality a b) =
      fun x => (a*b) * complementaryE x := by
  classical
  have hcard := EndpointSelfLoop.remaining_card i j hij
  have hrem : 0 < Fintype.card (Remaining i j) := by
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨k⟩ := Fintype.card_pos_iff.mp hrem
  have hne : (fun _ : Remaining i j => false) ≠ (fun _ => true) := by
    intro h
    exact Bool.false_ne_true (congrFun h k)
  funext x
  unfold gramTable pairSlice generalizedEquality
  simp only [fillPair_constant_iff,complement_constant_iff]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [h0,h1,h2,h3,Ne.symm hne,complementaryE,mul_comm]

theorem scaledComplementary_central (c : AlgebraicComplex) :
    Signature.CentralSupport (fun x => c * complementaryE x) := by
  intro x hx
  have h : ¬ (x 0 = x 1 ∧ x 2 = x 3 ∧ x 0 ≠ x 2) := by
    intro hp
    apply hx
    have hh : ∀ y : Fin 4 → Bool,
        y 0 = y 1 ∧ y 2 = y 3 ∧ y 0 ≠ y 2 → 2 * weight y = 4 := by
      decide +kernel
    exact hh x hp
  simp [complementaryE,h]

theorem scaledComplementary_ne_zero (c : AlgebraicComplex) (hc : c ≠ 0) :
    (fun x => c * complementaryE x) ≠ 0 := by
  intro hz
  have hh := congrFun hz ![false,false,true,true]
  exact hc (by simpa [complementaryE] using hh)

/-- A nonsingular four-port anti-diagonal matching product has four supported
central words; this actual output has exactly the two complementary words. -/
theorem scaledComplementary_not_matching (c : AlgebraicComplex) (hc : c ≠ 0) :
    ¬ WeightedMatching.IsProduct (fun x => c * complementaryE x) := by
  intro hm
  rcases MatchingComplement.quaternary_matching_three_cases hm with h | h | h
  · exact hc (by simpa [MatchingComplement.sixWord,complementaryE] using h.1)
  · exact h.2.2.2.2.1 (by simp [MatchingComplement.sixWord,complementaryE])
  · exact h.2.2.2.2.1 (by simp [MatchingComplement.sixWord,complementaryE])

end
end Paper2.RelativeEO
