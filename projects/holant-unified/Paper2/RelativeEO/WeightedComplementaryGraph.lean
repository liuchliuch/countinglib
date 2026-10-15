import Paper2.RelativeEO.ComplementaryCarrierGraph

/-! The two-copy native-X normalization of a complementary quaternary in the
canonical ordered support 0101/1010. Every p,q factor is retained: the graph
output is exactly p*q times the unweighted 0011/1100 table. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput
open scoped BigOperators

noncomputable def weightedComplementary (p q : AlgebraicComplex) : Signature AlgebraicComplex 4 :=
  fun x => if x 0 = false ∧ x 1 = true ∧ x 2 = false ∧ x 3 = true then p
    else if x 0 = true ∧ x 1 = false ∧ x 2 = true ∧ x 3 = false then q else 0

def quadWord (a b c d : Bool) : Fin 4 → Bool :=
  Fin.cases a (Fin.cases b (Fin.cases c (fun _ => d)))

@[simp] theorem weightedComplementary_quad (p q : AlgebraicComplex) (a b c d : Bool) :
    weightedComplementary p q (quadWord a b c d) =
      if a = false ∧ b = true ∧ c = false ∧ d = true then p
      else if a = true ∧ b = false ∧ c = true ∧ d = false then q else 0 := rfl

def weightedPorts : (Σ _ : Bool, Fin 4) ≃ (Fin 4 ⊕ (Fin 2 × Bool)) where
  toFun p := if p.1 then
    Fin.cases (.inl 3) (Fin.cases (.inl 1) (Fin.cases (.inr (0, true)) (fun _ => .inr (1, true)))) p.2
    else Fin.cases (.inl 0) (Fin.cases (.inl 2) (Fin.cases (.inr (0, false)) (fun _ => .inr (1, false)))) p.2
  invFun q := match q with
    | .inl i => Fin.cases ⟨false, 0⟩ (Fin.cases ⟨true, 1⟩
      (Fin.cases ⟨false, 1⟩ (fun _ => ⟨true, 0⟩))) i
    | .inr (i, b) => ⟨b, Fin.cases 2 (fun _ => 3) i⟩
  left_inv := by rintro ⟨b, i⟩; cases b <;> fin_cases i <;> rfl
  right_inv := by
    intro q
    rcases q with i | ⟨i, b⟩
    · fin_cases i <;> rfl
    · fin_cases i <;> cases b <;> rfl

noncomputable def weightedFinite (p q : AlgebraicComplex) :
    FiniteNetwork AlgebraicComplex Bool (Fin 2) 4 where
  arity _ := 4
  ports := weightedPorts
  vertex _ := weightedComplementary p q
  edge _ := Signature.disequality

noncomputable def weightedNetwork (p q : AlgebraicComplex) : Network AlgebraicComplex 4 :=
  (weightedFinite p q).toNetwork

def pairAssignmentEquiv : (Fin 2 → Bool) ≃ (Bool × Bool) where
  toFun z := (z 0, z 1)
  invFun p := Fin.cases p.1 (fun _ => p.2)
  left_inv := by intro z; funext i; fin_cases i <;> rfl
  right_inv := by intro p; rfl

theorem weightedNetwork_denote (p q : AlgebraicComplex) :
    (weightedNetwork p q).denote = fun x => (p * q) * complementaryE x := by
  classical
  letI : DecidableEq (Fin 2) := Classical.decEq (Fin 2)
  funext x
  rw [weightedNetwork, FiniteNetwork.denote_toNetwork]
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  change (∑ z : Fin 2 → Bool, ∏ v : Bool,
    weightedComplementary p q (fun i => Sum.elim x
      (fun a : Fin 2 × Bool => if a.2 then !(z a.1) else z a.1) (weightedPorts ⟨v, i⟩))) = _
  rw [← pairAssignmentEquiv.symm.sum_comp, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fintype.prod_bool]
  change
    (weightedComplementary p q (quadWord (x 3) (x 1) false false) *
        weightedComplementary p q (quadWord (x 0) (x 2) true true) +
      weightedComplementary p q (quadWord (x 3) (x 1) false true) *
        weightedComplementary p q (quadWord (x 0) (x 2) true false)) +
    (weightedComplementary p q (quadWord (x 3) (x 1) true false) *
        weightedComplementary p q (quadWord (x 0) (x 2) false true) +
      weightedComplementary p q (quadWord (x 3) (x 1) true true) *
        weightedComplementary p q (quadWord (x 0) (x 2) false false)) = _
  simp only [weightedComplementary_quad]
  cases hx0 : x 0 <;> cases hx1 : x 1 <;> cases hx2 : x 2 <;> cases hx3 : x 3 <;>
    simp [complementaryE, hx0, hx1, hx2, hx3] <;> ring

theorem weightedNetwork_uses {F : SignatureFamily AlgebraicComplex} (p q : AlgebraicComplex)
    (hD : (⟨4, weightedComplementary p q⟩ : AnySignature AlgebraicComplex) ∈ F) :
    (weightedNetwork p q).Uses F := fun _ => hD

theorem weightedNetwork_nativeX (p q : AlgebraicComplex) :
    (weightedNetwork p q).NativeX := fun _ => rfl

end Paper2.RelativeEO
