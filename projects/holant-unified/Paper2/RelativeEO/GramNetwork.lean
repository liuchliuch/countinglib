import Paper2.RelativeEO.GramVariance
import Paper2.RelativeEO.WeightedComplementaryGraph

/-! The actual two-copy native-X mating with exactly two ordered external
ports on each copy. Every other original port is joined to its corresponding
port on the other copy. No conjugation is present in this network definition. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
noncomputable section
open Paper2.Tractable Paper2.ExactInput EndpointSelfLoop
open scoped BigOperators
variable {n : ℕ} {K : Type*}
local instance (i j : Fin n) : DecidableEq (Remaining i j) := Classical.decEq _

noncomputable def fillPair (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (z : Remaining i j → Bool) : Fin n → Bool :=
  fun k => Sum.elim z (fun t => if t then b else a) (splitPorts i j hij k)

@[simp] theorem fillPair_first (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (z : Remaining i j → Bool) : fillPair i j hij a b z i = a := by
  classical
  simp [fillPair,splitPorts]

@[simp] theorem fillPair_second (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (z : Remaining i j → Bool) : fillPair i j hij a b z j = b := by
  classical
  simp [fillPair,splitPorts,Ne.symm hij]

@[simp] theorem fillPair_other (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (z : Remaining i j → Bool) (k : Remaining i j) : fillPair i j hij a b z k.val = z k := by
  classical
  simp [fillPair,splitPorts,k.property.1,k.property.2]

theorem fillPair_eta (i j : Fin n) (hij : i ≠ j) (x : Fin n → Bool) :
    fillPair i j hij (x i) (x j) (fun k => x k.val) = x := by
  classical
  funext k
  by_cases hi : k = i
  · subst k; simp
  · by_cases hj : k = j
    · subst k; simp
    · exact fillPair_other i j hij (x i) (x j) _ ⟨k,hi,hj⟩

@[simp] theorem fillPair_complement (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (z : Remaining i j → Bool) :
    fillPair i j hij (!a) (!b) (fun k => !(z k)) = fun k => !(fillPair i j hij a b z k) := by
  funext k
  unfold fillPair
  cases splitPorts i j hij k with
  | inl k => rfl
  | inr t => cases t <;> rfl

noncomputable def pairAssignment (i j : Fin n) (hij : i ≠ j) :
    ((Bool × Bool) × (Remaining i j → Bool)) ≃ (Fin n → Bool) where
  toFun p := fillPair i j hij p.1.1 p.1.2 p.2
  invFun x := ((x i,x j),fun k => x k.val)
  left_inv := by
    rintro ⟨⟨a,b⟩,z⟩
    simp only [fillPair_first,fillPair_second,fillPair_other]
  right_inv := fillPair_eta i j hij

noncomputable def pairSlice (i j : Fin n) (hij : i ≠ j) (f : Signature K n)
    (a b : Bool) : (Remaining i j → Bool) → K := fun z => f (fillPair i j hij a b z)

/-- Full-table masses coincide exactly with the ordered slice squared norms. -/
theorem pairMass_slice (i j : Fin n) (hij : i ≠ j) (f : Signature ℂ n) (a b : Bool) :
    pairMass f i j a b = ∑ z, Complex.normSq (pairSlice i j hij f a b z) := by
  classical
  rw [pairMass,← (pairAssignment i j hij).sum_comp]
  simp only [Fintype.sum_prod_type,Fintype.sum_bool,pairAssignment,fillPair_first,fillPair_second]
  cases a <;> cases b <;> simp [pairSlice]

/-- The external order is first-copy port i,j, then second-copy port i,j. -/
def quadPortEquiv : (Bool × Bool) ≃ Fin 4 where
  toFun p := if p.1 then (if p.2 then 3 else 2) else (if p.2 then 1 else 0)
  invFun k := Fin.cases (false,false) (Fin.cases (false,true)
    (Fin.cases (true,false) (fun _ => (true,true)))) k
  left_inv := by rintro ⟨a,b⟩; cases a <;> cases b <;> rfl
  right_inv := by intro k; fin_cases k <;> rfl

noncomputable def gramShuffle (i j : Fin n) :
    (Bool × (Remaining i j ⊕ Bool)) ≃ (Fin 4 ⊕ (Remaining i j × Bool)) where
  toFun p := match p.2 with
    | .inl k => .inr (k,p.1)
    | .inr b => .inl (quadPortEquiv (p.1,b))
  invFun p := match p with
    | .inl k => ((quadPortEquiv.symm k).1,.inr (quadPortEquiv.symm k).2)
    | .inr (k,v) => (v,.inl k)
  left_inv := by
    rintro ⟨v,k | b⟩
    · rfl
    · simp only [Equiv.symm_apply_apply]
  right_inv := by
    rintro (k | ⟨k,v⟩)
    · exact congrArg Sum.inl (quadPortEquiv.apply_symm_apply k)
    · rfl

noncomputable def gramPorts (i j : Fin n) (hij : i ≠ j) :
    (Σ _ : Bool, Fin n) ≃ (Fin 4 ⊕ (Remaining i j × Bool)) :=
  ((Equiv.sigmaEquivProd Bool (Fin n)).trans
    (Equiv.prodCongr (Equiv.refl Bool) (splitPorts i j hij))).trans (gramShuffle i j)

noncomputable def gramFinite [CommSemiring K] (i j : Fin n) (hij : i ≠ j)
    (f : Signature K n) : FiniteNetwork K Bool (Remaining i j) 4 where
  arity _ := n
  ports := gramPorts i j hij
  vertex _ := f
  edge _ := Signature.disequality

noncomputable def gramTable [CommSemiring K] (i j : Fin n) (hij : i ≠ j)
    (f : Signature K n) : Signature K 4 := fun x =>
  ∑ z : Remaining i j → Bool,
    pairSlice i j hij f (x 0) (x 1) z *
      pairSlice i j hij f (x 2) (x 3) (fun k => !(z k))

/-- Exact denotation, with no omitted summands or normalization constants. -/
theorem gramFinite_denote [CommSemiring K] (i j : Fin n) (hij : i ≠ j) (f : Signature K n) :
    (gramFinite i j hij f).toNetwork.denote = gramTable i j hij f := by
  classical
  funext x
  rw [FiniteNetwork.denote_toNetwork,FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  change (∑ z : Remaining i j → Bool, ∏ v : Bool, f (fun k => Sum.elim x
    (fun p : Remaining i j × Bool => if p.2 then !(z p.1) else z p.1)
      (gramPorts i j hij ⟨v,k⟩))) = _
  unfold gramTable
  apply Finset.sum_congr rfl
  intro z _
  have ha (v : Bool) : (fun k => Sum.elim x
      (fun p : Remaining i j × Bool => if p.2 then !(z p.1) else z p.1)
        (gramPorts i j hij ⟨v,k⟩)) =
      fillPair i j hij (x (quadPortEquiv (v,false))) (x (quadPortEquiv (v,true)))
        (fun k => if v then !(z k) else z k) := by
    funext k
    change Sum.elim x (fun p : Remaining i j × Bool => if p.2 then !(z p.1) else z p.1)
      (match splitPorts i j hij k with
        | .inl r => .inr (r,v)
        | .inr b => .inl (quadPortEquiv (v,b))) =
      Sum.elim (fun r => if v then !(z r) else z r)
        (fun b => if b then x (quadPortEquiv (v,true)) else x (quadPortEquiv (v,false)))
        (splitPorts i j hij k)
    cases splitPorts i j hij k with
    | inl k => rfl
    | inr b => cases b <;> rfl
  rw [Fintype.prod_bool,ha true,ha false]
  exact mul_comm _ _

/-- The graph uses two occurrences of the original literal member and only X. -/
theorem gramTable_realized {F : SignatureFamily AlgebraicComplex}
    (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (hf : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NativeNetworkRealizesUpTo F (gramTable i j hij f) := by
  refine ⟨(gramFinite i j hij f).toNetwork,(fun _ => hf),(fun _ => rfl),1,one_ne_zero,?_⟩
  simpa only [one_mul] using gramFinite_denote i j hij f

end
end Paper2.RelativeEO
