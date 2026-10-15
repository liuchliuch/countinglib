import Paper2.TransversalCube.Table
import Paper2.NetworkRealization

namespace Paper2.TransversalCube
open scoped BigOperators
noncomputable section

/-- Incidences of the alternating-path construction. The two vertices are the
two Boolean values. Every first-copy pair except pair zero is wired twice. -/
def pathPort (m : ℕ) (v : Bool) (i : Ports m) : Fin 4 ⊕ (Edges m × Bool) :=
  if v then
    if i.2 then Fin.lastCases (.inl 3) (fun j => .inr ((j,false),true)) i.1
    else Fin.cases (.inl 2) (fun j => .inr ((j,true),true)) i.1
  else Fin.cases (.inl (if i.2 then 1 else 0))
    (fun j => .inr ((j,i.2),false)) i.1

def pathPortInv (m : ℕ) : Fin 4 ⊕ (Edges m × Bool) → (Σ _ : Bool, Ports m)
  | .inl i => ![⟨false,(0,false)⟩, ⟨false,(0,true)⟩,
      ⟨true,(0,false)⟩, ⟨true,(Fin.last m,true)⟩] i
  | .inr ((i,b),false) => ⟨false,(i.succ,b)⟩
  | .inr ((i,false),true) => ⟨true,(i.castSucc,true)⟩
  | .inr ((i,true),true) => ⟨true,(i.succ,false)⟩

def pathPorts (m : ℕ) : (Σ _ : Bool, Ports m) ≃ (Fin 4 ⊕ (Edges m × Bool)) where
  toFun := fun p => pathPort m p.1 p.2
  invFun := pathPortInv m
  left_inv := by
    rintro ⟨v,j,b⟩
    cases v <;> cases b
    · induction j using Fin.cases <;> simp [pathPort,pathPortInv]
    · induction j using Fin.cases <;> simp [pathPort,pathPortInv]
    · induction j using Fin.cases <;> simp [pathPort,pathPortInv]
    · induction j using Fin.lastCases <;> simp [pathPort,pathPortInv]
  right_inv := by
    rintro (i | ⟨⟨i,b⟩,v⟩)
    · fin_cases i <;> simp [pathPort,pathPortInv]
    · cases v <;> cases b <;> simp [pathPort,pathPortInv]

variable {K : Type*} [CommRing K] [IsDomain K] {m n : ℕ}

/-- The same mountain in its original ordered ports. The equivalence is used
only to describe the factors and to construct graph incidences. -/
def orderedMountain (e : Ports m ≃ Fin n) (a b c : K) (p q : Fin (m+1) → K) :
    Signature K n := fun x => mountain a b c p q (fun i => x (e i))

lemma constant_reindex_iff (e : Ports m ≃ Fin n) (x : Fin n → Bool) (t : Bool) :
    (fun i => x (e i)) = (fun _ => t) ↔ x = (fun _ => t) := by
  constructor
  · intro h; funext j; obtain ⟨i,rfl⟩ := e.surjective j; exact congrFun h i
  · rintro rfl; rfl

/-- Exact equality with the source's two endpoint delta tensors plus its
weighted anti-diagonal matching product, including the overall scalar. -/
lemma orderedMountain_eq_source (e : Ports m ≃ Fin n) (a b c : K)
    (p q : Fin (m+1) → K) (x : Fin n → Bool) :
    orderedMountain e a b c p q x =
      (if x = (fun _ => false) then a else 0) +
      (if x = (fun _ => true) then b else 0) +
      WeightedMatching.product ⟨m+1,e⟩ p q c x := by
  simp [orderedMountain,mountain,central,WeightedMatching.product,constant_reindex_iff]

/-- Two copies of exactly M, with all relabeling confined to the incidence map. -/
def finiteNetwork (e : Ports m ≃ Fin n) (M : Signature K n) :
    FiniteNetwork K Bool (Edges m) 4 where
  arity := fun _ => n
  ports := (Equiv.sigmaCongrRight (fun _ : Bool => e.symm)).trans (pathPorts m)
  vertex := fun _ => M
  edge := fun _ => Signature.disequality

lemma path_assignment (x : Fin 4 → Bool) (z : Edges m → Bool) (v : Bool) (i : Ports m) :
    Sum.elim x (fun q : Edges m × Bool => if q.2 then !(z q.1) else z q.1)
      (pathPort m v i) = (if v then rightWord x z i else leftWord x z i) := by
  rcases i with ⟨j,b⟩
  cases v <;> cases b
  · induction j using Fin.cases <;> simp [pathPort,leftWord]
  · induction j using Fin.cases <;> simp [pathPort,leftWord]
  · induction j using Fin.cases <;> simp [pathPort,rightWord]
  · induction j using Fin.lastCases <;> simp [pathPort,rightWord]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 20000 in
lemma finiteNetwork_denote (e : Ports m ≃ Fin n) (a b c : K)
    (p q : Fin (m+1) → K) :
    (finiteNetwork e (orderedMountain e a b c p q)).denote = contract a b c p q := by
  classical
  funext x
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  unfold contract
  simp only [finiteNetwork]
  refine Finset.sum_congr (by ext z; simp) ?_
  intro z _
  rw [Fintype.prod_bool]
  simp only [finiteNetwork,orderedMountain,Equiv.trans_apply,
    Equiv.sigmaCongrRight_apply,Equiv.symm_apply_apply,pathPorts]
  simp only [Equiv.coe_fn_mk, path_assignment, Bool.false_eq_true, ite_false, ite_true, term]
  exact mul_comm _ _

/-- A concrete native-X network, not merely a closure predicate. -/
def network (e : Ports m ≃ Fin n) (M : Signature K n) : Network K 4 :=
  (finiteNetwork e M).toNetwork

lemma network_uses (e : Ports m ≃ Fin n) (M : Signature K n)
    (F : SignatureFamily K) (hM : (⟨n,M⟩ : AnySignature K) ∈ F) :
    (network e M).Uses F := by
  intro v; exact hM

lemma network_nativeX (e : Ports m ≃ Fin n) (M : Signature K n) :
    (network e M).NativeX := by intro v; rfl

lemma network_denote (e : Ports m ≃ Fin n) (a b c : K)
    (p q : Fin (m+1) → K) :
    (network e (orderedMountain e a b c p q)).denote = contract a b c p q := by
  exact (FiniteNetwork.denote_toNetwork _).trans (finiteNetwork_denote e a b c p q)

lemma network_vertices (e : Ports m ≃ Fin n) (M : Signature K n) :
    (network e M).shape.vertices = 2 := by simp [network,FiniteNetwork.toNetwork]

lemma network_edges (e : Ports m ≃ Fin n) (M : Signature K n) :
    (network e M).shape.edges = 2*m := by
  simp [network,FiniteNetwork.toNetwork,Edges,Nat.mul_comm]

end
end Paper2.TransversalCube
