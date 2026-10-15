import Paper2.HeightOne.Cyclic.QuaternaryFourier
import Paper2.HeightOne.Dihedral.QuaternaryPrime
import Paper2.HighHeightNormalization.FiniteAttachments

/-! The two-copy graph used in the three-live-pair cyclic four-port branch.
Both internal wires are literal native X; the four exposed ports retain their
order. Graph substitution compiles already realized inputs without adjoining
an analytic Walsh table. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhaseCards Dihedral
open scoped BigOperators

private def twoCopyPorts : (Σ _ : Bool, Fin 4) ≃ (Fin 4 ⊕ (Bool × Bool)) where
  toFun
    | ⟨false, i⟩ => if i = 0 then .inl 0 else if i = 1 then .inl 1 else
        if i = 2 then .inr (false,false) else .inr (true,false)
    | ⟨true, i⟩ => if i = 0 then .inr (false,true) else if i = 1 then .inr (true,true) else
        if i = 2 then .inl 2 else .inl 3
  invFun
    | .inl i => if i = 0 then ⟨false,0⟩ else if i = 1 then ⟨false,1⟩ else
        if i = 2 then ⟨true,2⟩ else ⟨true,3⟩
    | .inr (false,false) => ⟨false,2⟩
    | .inr (true,false) => ⟨false,3⟩
    | .inr (false,true) => ⟨true,0⟩
    | .inr (true,true) => ⟨true,1⟩
  left_inv := by rintro ⟨b,i⟩; cases b <;> fin_cases i <;> rfl
  right_inv := by rintro (i | ⟨b,c⟩); fin_cases i <;> rfl; cases b <;> cases c <;> rfl

def twoCopyFiniteNetwork (f : Signature AlgebraicComplex 4) :
    FiniteNetwork AlgebraicComplex Bool Bool 4 where
  arity _ := 4
  ports := twoCopyPorts
  vertex _ := f
  edge _ := Signature.disequality

def twoCopyX (f : Signature AlgebraicComplex 4) : Signature AlgebraicComplex 4 :=
  fun x => ∑ a : Bool, ∑ b : Bool,
    f ![x 0,x 1,a,b] * f ![!a,!b,x 2,x 3]

lemma twoCopyFiniteNetwork_denote (f : Signature AlgebraicComplex 4) :
    (twoCopyFiniteNetwork f).denote = twoCopyX f := by
  classical
  letI : DecidableEq Bool := fun _ _ => Classical.propDecidable _
  funext x
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  let e : (Bool → Bool) ≃ (Bool × Bool) := {
    toFun := fun z => (z false,z true)
    invFun := fun p b => if b then p.2 else p.1
    left_inv := by intro z; funext b; cases b <;> simp
    right_inv := by intro p; simp }
  let G : (Bool → Bool) → AlgebraicComplex := fun z =>
    ∏ v : Bool, (twoCopyFiniteNetwork f).vertex v (fun i => Sum.elim x
      (fun q : Bool × Bool => if q.2 then !(z q.1) else z q.1)
      ((twoCopyFiniteNetwork f).ports ⟨v,i⟩))
  have hG : (∑ z : Bool → Bool, ∏ v : Bool,
      (twoCopyFiniteNetwork f).vertex v (fun i => Sum.elim x
        (fun q : Bool × Bool => if q.2 then !(z q.1) else z q.1)
        ((twoCopyFiniteNetwork f).ports ⟨v,i⟩))) = ∑ z, G z := by rfl
  convert_to (∑ z, G z) = twoCopyX f x using 1
  · apply Finset.sum_congr (by ext; simp)
    intro z _
    dsimp only [G]
    apply Finset.prod_congr (by ext; simp)
    intro v _
    cases v <;> apply congrArg f <;> funext i <;> fin_cases i <;>
      simp [twoCopyFiniteNetwork,twoCopyPorts]
  rw [← e.symm.sum_comp G]
  simp only [Fintype.sum_prod_type, G, Fintype.prod_bool]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  change f (fun i => Sum.elim x
      (fun q : Bool × Bool => if q.2 then !(e.symm (a,b) q.1) else e.symm (a,b) q.1)
      (twoCopyPorts ⟨true,i⟩)) *
    f (fun i => Sum.elim x
      (fun q : Bool × Bool => if q.2 then !(e.symm (a,b) q.1) else e.symm (a,b) q.1)
      (twoCopyPorts ⟨false,i⟩)) = _
  have hfalse : (fun i => Sum.elim x
      (fun q : Bool × Bool => if q.2 then !(e.symm (a,b) q.1) else e.symm (a,b) q.1)
      (twoCopyPorts ⟨false,i⟩)) = ![x 0,x 1,a,b] := by funext i; fin_cases i <;> simp [e,twoCopyPorts]
  have htrue : (fun i => Sum.elim x
      (fun q : Bool × Bool => if q.2 then !(e.symm (a,b) q.1) else e.symm (a,b) q.1)
      (twoCopyPorts ⟨true,i⟩)) = ![!a,!b,x 2,x 3] := by funext i; fin_cases i <;> simp [e,twoCopyPorts]
  rw [hfalse,htrue,mul_comm]

theorem twoCopyX_realizable {F : SignatureFamily AlgebraicComplex}
    (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable F f) :
    NetworkRealizable F (twoCopyX f) := by
  have hr := NetworkRealizable.substitute (F := F) (twoCopyFiniteNetwork f).toNetwork
    (fun _ => rfl) (fun _ => hf)
  rw [FiniteNetwork.denote_toNetwork,twoCopyFiniteNetwork_denote] at hr
  exact hr

def inverseBlockPorts (i : Fin 3) : Fin 4 → Fin 4 :=
  ![![0,1,2,3],![0,2,1,3],![0,2,3,1]] i

@[simp] lemma blockPorts_inverse_apply (i : Fin 3) (j : Fin 4) :
    (blockPorts i).symm j = inverseBlockPorts i j := by
  apply (blockPorts i).injective
  rw [Equiv.apply_symm_apply]
  fin_cases i <;> fin_cases j <;> simp [blockPorts,inverseBlockPorts,otherFirst,otherSecond]

/-- Choose the original complementary pair as the ordered first block. -/
def twoCopyAt (i : Fin 3) (f : Signature AlgebraicComplex 4) : Signature AlgebraicComplex 4 :=
  twoCopyX (Tensor.reindex (blockPorts i).symm f)

theorem twoCopyAt_realizable {F : SignatureFamily AlgebraicComplex}
    (i : Fin 3) (f : Signature AlgebraicComplex 4) (hf : NetworkRealizable F f) :
    NetworkRealizable F (twoCopyAt i f) :=
  twoCopyX_realizable _ (hf.reindex (blockPorts i).symm)

lemma twoCopyX_scalar (c : AlgebraicComplex) (f : Signature AlgebraicComplex 4) :
    twoCopyX (fun x => c * f x) = fun x => c ^ 2 * twoCopyX f x := by
  funext x
  simp only [twoCopyX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

end
end Paper2.HeightOne.Cyclic
