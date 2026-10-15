import Paper2.HeightThree.LoopGeometry
import Paper2.GadgetTrace
import Paper2.Certificates.Q6CardNaturality

/-! Every legal four-wire specification is an actual two-vertex native-X
network. The external order is exactly (left0,left1,right0,right1). -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightThree
open Certificates.Q6
noncomputable section

abbrev Interior (a b : Port) := {v : Port // v ∈ Finset.univ \ {a,b}}

noncomputable def remainingInterior (a b : Port) : EndpointSelfLoop.Remaining a b ≃ Interior a b where
  toFun v := ⟨v.val,by simpa only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_and,not_or] using v.property⟩
  invFun v := ⟨v.val,by simpa only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_insert,Finset.mem_singleton,true_and,not_or] using v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def pairSplit (a b : Port) (hab : a ≠ b) : Port ≃ (Interior a b ⊕ Bool) :=
  (EndpointSelfLoop.splitPorts a b hab).trans
    (Equiv.sumCongr (remainingInterior a b) (Equiv.refl Bool))

abbrev LeftInterior (s : CardSpec) := Interior s.left0 s.left1
abbrev RightInterior (s : CardSpec) := Interior s.right0 s.right1

noncomputable def interiorWiring (s : CardSpec) (hs : RawValidCardSpec s) :
    LeftInterior s ≃ RightInterior s :=
  Equiv.ofBijective (fun v => ⟨s.wiring v.val,by
    change s.wiring v.val ∈ internalRight s
    rw [← hs.2.2.2]
    exact Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩⟩) (by
      constructor
      · intro u v h
        exact Subtype.ext (hs.2.2.1.1 (congrArg Subtype.val h))
      · intro v
        have hv := v.property
        change v.val ∈ internalRight s at hv
        rw [← hs.2.2.2] at hv
        obtain ⟨u,hu,he⟩ := Finset.mem_image.mp hv
        exact ⟨⟨u,hu⟩,Subtype.ext he⟩)

noncomputable def cardSplit (s : CardSpec) (hs : RawValidCardSpec s)
    (v : Bool) : Port ≃ (LeftInterior s ⊕ Bool) :=
  if v then (pairSplit s.right0 s.right1 hs.2.1).trans
    (Equiv.sumCongr (interiorWiring s hs).symm (Equiv.refl Bool))
  else pairSplit s.left0 s.left1 hs.1

def boundaryIndex (v b : Bool) : Fin 4 := if v then (if b then 3 else 2) else (if b then 1 else 0)
def boundaryPair : Fin 4 → Bool × Bool := ![(false,false),(false,true),(true,false),(true,true)]

lemma boundaryPair_index (v b : Bool) : boundaryPair (boundaryIndex v b) = (v,b) := by
  cases v <;> cases b <;> rfl
lemma boundaryIndex_pair (i : Fin 4) : boundaryIndex (boundaryPair i).1 (boundaryPair i).2 = i := by
  fin_cases i <;> rfl

noncomputable def cardPortShuffle (s : CardSpec) :
    (Σ _ : Bool, LeftInterior s ⊕ Bool) ≃ (Fin 4 ⊕ (LeftInterior s × Bool)) where
  toFun p := match p.2 with
    | .inl e => .inr (e,p.1)
    | .inr b => .inl (boundaryIndex p.1 b)
  invFun q := match q with
    | .inl i => ⟨(boundaryPair i).1,.inr (boundaryPair i).2⟩
    | .inr (e,v) => ⟨v,.inl e⟩
  left_inv := by
    rintro ⟨v,e|b⟩
    · rfl
    · simp only [boundaryPair_index]
  right_inv := by
    rintro (i | ⟨e,v⟩)
    · simp only [boundaryIndex_pair]
    · rfl

variable {K : Type} [CommSemiring K]

noncomputable def cardFiniteNetwork (s : CardSpec) (hs : RawValidCardSpec s)
    (M : Signature K 6) : FiniteNetwork K Bool (LeftInterior s) 4 where
  arity := fun _ => 6
  ports := (Equiv.sigmaCongrRight (cardSplit s hs)).trans (cardPortShuffle s)
  vertex := fun _ => M
  edge := fun _ => Signature.disequality

noncomputable def cardNetwork (s : CardSpec) (hs : RawValidCardSpec s)
    (M : Signature K 6) : Network K 4 := (cardFiniteNetwork s hs M).toNetwork

lemma cardNetwork_uses (s : CardSpec) (hs : RawValidCardSpec s)
    (M : Signature K 6) (F : SignatureFamily K) (hM : (⟨6,M⟩ : AnySignature K) ∈ F) :
    (cardNetwork s hs M).Uses F := by intro v; exact hM

lemma cardNetwork_nativeX (s : CardSpec) (hs : RawValidCardSpec s) (M : Signature K 6) :
    (cardNetwork s hs M).NativeX := by intro e; rfl

noncomputable def cardWord (s : CardSpec) (hs : RawValidCardSpec s)
    (x : Fin 4 → Bool) (z : LeftInterior s → Bool) (v : Bool) : Port → Bool := fun p =>
  Sum.elim (fun e => if v then !(z e) else z e) (fun b => x (boundaryIndex v b)) (cardSplit s hs v p)

lemma card_assignment (s : CardSpec) (hs : RawValidCardSpec s)
    (x : Fin 4 → Bool) (z : LeftInterior s → Bool) (v : Bool) (p : Port) :
    Sum.elim x (fun q : LeftInterior s × Bool => if q.2 then !(z q.1) else z q.1)
      ((cardFiniteNetwork s hs (0 : Signature K 6)).ports ⟨v,p⟩) = cardWord s hs x z v p := by
  change Sum.elim x (fun q : LeftInterior s × Bool => if q.2 then !(z q.1) else z q.1)
    (match cardSplit s hs v p with
     | .inl e => .inr (e,v)
     | .inr b => .inl (boundaryIndex v b)) =
      Sum.elim (fun e => if v then !(z e) else z e) (fun b => x (boundaryIndex v b)) (cardSplit s hs v p)
  cases cardSplit s hs v p <;> rfl

lemma cardNetwork_denote (s : CardSpec) (hs : RawValidCardSpec s) (M : Signature K 6)
    (x : Fin 4 → Bool) : (cardNetwork s hs M).denote x =
      ∑ z : LeftInterior s → Bool, M (cardWord s hs x z false) * M (cardWord s hs x z true) := by
  rw [cardNetwork,FiniteNetwork.denote_toNetwork]
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  refine Finset.sum_congr (by ext z; simp) ?_
  intro z _
  rw [Fintype.prod_bool]
  change M (fun p => Sum.elim x _ ((cardFiniteNetwork s hs (0 : Signature K 6)).ports ⟨true,p⟩)) *
    M (fun p => Sum.elim x _ ((cardFiniteNetwork s hs (0 : Signature K 6)).ports ⟨false,p⟩)) = _
  simp only [card_assignment]
  exact mul_comm _ _

end
end Paper2.HeightThree
