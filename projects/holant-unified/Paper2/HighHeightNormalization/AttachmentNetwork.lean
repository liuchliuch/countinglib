import Paper2.HighHeightNormalization.BinaryMating
import Paper2.NetworkSubstitution
import Paper2.ExactInput.GadgetAugmentation

/-! Actual finite native-X graph for a binary attachment in the original
algebraic coefficient field, with one old vertex and one binary vertex. -/
namespace Paper2.HighHeightNormalization
open MatchingPropagation CommonPhase EndpointSelfLoop Tractable ExactInput
variable {K : Type} [CommSemiring K] {n : ℕ}

/-- An ordered binary kernel as the actual two-port input table. -/
def binaryTable (B : Kernel K) : Signature K 2 := fun x => B (x 0) (x 1)

/-- The literal two-state native-X attachment, with the new external bit at a. -/
noncomputable def attachment (a : Fin n) (B : Kernel K) (M : Signature K n) : Signature K n :=
  fun x => ∑ t : Bool, M (Function.update x a t) * B (!t) (x a)

private def attachmentPorts (a : Fin n) :
    (Σ v : Bool, Fin (if v then 2 else n)) ≃ (Fin n ⊕ (Unit × Bool)) where
  toFun
    | ⟨false,i⟩ => if i = a then .inr ((),false) else .inl i
    | ⟨true,i⟩ => if i = (0 : Fin 2) then .inr ((),true) else .inl a
  invFun
    | .inl i => if i = a then ⟨true,(1 : Fin 2)⟩ else ⟨false,i⟩
    | .inr ((),false) => ⟨false,a⟩
    | .inr ((),true) => ⟨true,(0 : Fin 2)⟩
  left_inv := by
    rintro ⟨v,i⟩
    cases v
    · by_cases h : i = a <;> simp [h]
    · fin_cases i <;> simp
  right_inv := by
    rintro (i | ⟨u,b⟩)
    · by_cases h : i = a <;> simp [h]
    · cases u; cases b <;> simp

/-- Two actual vertices and one actual native-X edge. -/
noncomputable def attachmentFiniteNetwork (a : Fin n) (B : Kernel K)
    (M : Signature K n) : FiniteNetwork K Bool Unit n where
  arity v := if v then 2 else n
  ports := attachmentPorts a
  vertex
    | false => M
    | true => binaryTable B
  edge _ := Signature.disequality

private theorem attachment_assignment_false (a : Fin n) (x : Fin n → Bool)
    (t : Bool) :
    (fun i : Fin n => Sum.elim x (fun q : Unit × Bool => if q.2 then !t else t)
      (attachmentPorts a ⟨false,i⟩)) = Function.update x a t := by
  funext i
  by_cases h : i = a <;> simp [attachmentPorts,Function.update,h]

set_option backward.isDefEq.respectTransparency false in
/-- The graph denotation is the actual finite sum, with no extra scalar. -/
theorem attachmentFiniteNetwork_denote (a : Fin n) (B : Kernel K) (M : Signature K n) :
    (attachmentFiniteNetwork a B M).denote = attachment a B M := by
  classical
  letI : DecidableEq Unit := fun _ _ => Classical.propDecidable _
  funext x
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  change _ = ∑ t : Bool, M (Function.update x a t) * B (!t) (x a)
  apply Fintype.sum_equiv (Equiv.funUnique Unit Bool)
  intro z
  have hz : z = fun _ => z () := by funext u; cases u; rfl
  rw [hz, Fintype.prod_bool]
  change
    (binaryTable B (fun i : Fin 2 => Sum.elim x
      (fun q : Unit × Bool => if q.2 then !(z ()) else z ())
      (attachmentPorts a ⟨true,i⟩))) *
    M (fun i : Fin n => Sum.elim x
      (fun q : Unit × Bool => if q.2 then !(z ()) else z ())
      (attachmentPorts a ⟨false,i⟩)) = _
  rw [attachment_assignment_false]
  simp [binaryTable,attachmentPorts,Equiv.funUnique,Equiv.piUnique,mul_comm]

/-- This graph uses only the supplied complete mountain and the supplied
ordered binary factor. The central layer is never treated as an input vertex. -/
theorem attachment_realizable {F : SignatureFamily K} (a : Fin n) (B : Kernel K)
    (M : Signature K n) (hM : (⟨n,M⟩ : AnySignature K) ∈ F)
    (hB : (⟨2,binaryTable B⟩ : AnySignature K) ∈ F) :
    NetworkRealizable F (attachment a B M) := by
  refine ⟨n,(attachmentFiniteNetwork a B M).toNetwork,Equiv.refl _,?_,?_,?_⟩
  · intro v
    change (⟨_,(attachmentFiniteNetwork a B M).vertex ((Fintype.equivFin Bool).symm v)⟩ :
      AnySignature K) ∈ F
    cases (Fintype.equivFin Bool).symm v
    · exact hM
    · exact hB
  · intro e
    rfl
  · rw [FiniteNetwork.denote_toNetwork]
    exact attachmentFiniteNetwork_denote a B M

end Paper2.HighHeightNormalization
