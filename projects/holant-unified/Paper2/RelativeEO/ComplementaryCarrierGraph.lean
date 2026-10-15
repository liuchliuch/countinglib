import Paper2.RelativeEO.DirectedPair
import Paper2.GadgetTrace
import Paper2.NetworkRealization

/-! The actual two-vertex native-X carrier from Paper 2's complementary
quaternary argument. Boundary order is A=(a1,a3), P=(b1,a2), Y=(b2,b3).
No pins are inserted as graph resources. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput
open scoped BigOperators

noncomputable def complementaryE : Signature AlgebraicComplex 4 :=
  fun x => if x 0 = x 1 ∧ x 2 = x 3 ∧ x 0 ≠ x 2 then 1 else 0

def carrierPorts : (Σ _ : Bool, Fin 4) ≃ (Fin 6 ⊕ (Unit × Bool)) where
  toFun p := if p.1 then
    Fin.cases (.inl 2) (Fin.cases (.inl 4) (Fin.cases (.inl 5) (fun _ => .inr ((), true)))) p.2
    else Fin.cases (.inl 0) (Fin.cases (.inl 3) (Fin.cases (.inl 1) (fun _ => .inr ((), false)))) p.2
  invFun q := match q with
    | .inl i => Fin.cases ⟨false, 0⟩ (Fin.cases ⟨false, 2⟩
      (Fin.cases ⟨true, 0⟩ (Fin.cases ⟨false, 1⟩
        (Fin.cases ⟨true, 1⟩ (fun _ => ⟨true, 2⟩))))) i
    | .inr (_, b) => ⟨b, 3⟩
  left_inv := by rintro ⟨b, i⟩; cases b <;> fin_cases i <;> rfl
  right_inv := by
    intro q
    rcases q with i | ⟨u, b⟩
    · fin_cases i <;> rfl
    · cases u; cases b <;> rfl

noncomputable def complementaryCarrierFinite : FiniteNetwork AlgebraicComplex Bool Unit 6 where
  arity _ := 4
  ports := carrierPorts
  vertex _ := complementaryE
  edge _ := Signature.disequality

noncomputable def complementaryCarrier : Network AlgebraicComplex 6 :=
  complementaryCarrierFinite.toNetwork

theorem complementaryCarrier_uses {F : SignatureFamily AlgebraicComplex}
    (hE : (⟨4, complementaryE⟩ : AnySignature AlgebraicComplex) ∈ F) :
    complementaryCarrier.Uses F := fun _ => hE

theorem complementaryCarrier_nativeX : complementaryCarrier.NativeX := fun _ => rfl

/-- The unique input word selected after wiring an ordered Δ through native X. -/
def pairTen : Fin 2 → Bool := fun i => i == 0

theorem directedPair_complement_indicator (a : Fin 2 → Bool) :
    directedPair (fun i => !(a i)) = if a = pairTen then 1 else 0 := by
  have he : (Bool.not (a 0) = false ∧ Bool.not (a 1) = true) ↔ a = pairTen := by
    constructor
    · intro h
      funext i
      fin_cases i
      · cases ha : a 0 <;> simp_all [pairTen]
      · cases ha : a 1 <;> simp_all [pairTen]
    · rintro rfl
      decide
  simp only [directedPair, he]

/-- Feeding Δ into the A block selects exactly the opposite ordered word. -/
theorem feed_directedPair (f : (Fin 2 → Bool) → AlgebraicComplex) :
    (∑ a : Fin 2 → Bool, directedPair (fun i => !(a i)) * f a) = f pairTen := by
  simp_rw [directedPair_complement_indicator]
  simp

/-- Actual finite graph evaluation at the selected A word, in the displayed
ordered P,Y blocks. There is one internal X edge and two E-labelled vertices. -/
theorem complementaryCarrier_selected (p y : Fin 2 → Bool) :
    complementaryCarrier.denote (Fin.append pairTen (Fin.append p y)) =
      directedPair p * directedPair y := by
  classical
  letI : DecidableEq Unit := Classical.decEq Unit
  rw [complementaryCarrier, FiniteNetwork.denote_toNetwork]
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  change (∑ z : Unit → Bool, ∏ v : Bool,
    complementaryE (fun i => Sum.elim (Fin.append pairTen (Fin.append p y))
      (fun q : Unit × Bool => if q.2 then !(z q.1) else z q.1) (carrierPorts ⟨v, i⟩))) = _
  rw [← (Equiv.funUnique Unit Bool).symm.sum_comp, Fintype.sum_bool]
  simp only [Fintype.prod_bool]
  change
    (if p 0 = y 0 ∧ y 1 = false ∧ p 0 ≠ y 1 then (1 : AlgebraicComplex) else 0) *
      (if true = p 1 ∧ false = true ∧ true ≠ false then 1 else 0) +
    (if p 0 = y 0 ∧ y 1 = true ∧ p 0 ≠ y 1 then (1 : AlgebraicComplex) else 0) *
      (if true = p 1 ∧ false = false ∧ true ≠ false then 1 else 0) =
        directedPair p * directedPair y
  cases hp0 : p 0 <;> cases hp1 : p 1 <;>
    cases hy0 : y 0 <;> cases hy1 : y 1 <;>
    simp [directedPair, hp0, hp1, hy0, hy1]

/-- The exact carrier identity, derived from the graph sum and ordered Δ;
this does not assert unrestricted Δ or either unary is directly realizable. -/
theorem complementaryCarrier_step (p y : Fin 2 → Bool) :
    (∑ a : Fin 2 → Bool, directedPair (fun i => !(a i)) *
      complementaryCarrier.denote (Fin.append a (Fin.append p y))) =
      directedPair p * directedPair y := by
  rw [feed_directedPair, complementaryCarrier_selected]

end Paper2.RelativeEO
