import Paper2.DegreeCSP.Model
import Paper2.RelativeEO.GeneralizedEqualityGadget

/-! Native-X graph constructions for arbitrary multiples of one fixed
equality arity. The complementary quaternary obtained from two equalities
merges two blocks without changing their common external Boolean value. -/
namespace Paper2.DegreeCSP
open scoped BigOperators Classical
open Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

theorem equality_complement (n : ℕ) (x : Fin n → Bool) :
    equality (K := AlgebraicComplex) n (fun i => !(x i)) = equality n x := by
  have hfalse : (fun i => !(x i)) = (fun _ => false) ↔ x = (fun _ => true) := by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      cases hx : x i <;> simp_all
    · rintro rfl
      simp
  have htrue : (fun i => !(x i)) = (fun _ => true) ↔ x = (fun _ => false) := by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      cases hx : x i <;> simp_all
    · rintro rfl
      simp
  rw [equality_eq,equality_eq]
  simp only [hfalse,htrue]
  exact add_comm _ _

theorem equality_reindex (n m : ℕ) (e : Fin n ≃ Fin m) :
    Tensor.reindex e (equality (K := AlgebraicComplex) n) = equality m := by
  funext x
  have h (b : Bool) : (fun i => x (e i)) = (fun _ => b) ↔ x = (fun _ => b) := by
    constructor
    · intro hh
      funext i
      simpa only [e.apply_symm_apply] using congrFun hh (e.symm i)
    · rintro rfl
      rfl
  simp only [Tensor.reindex_apply,equality_eq,h]

theorem equality_realizable_congr (F : SignatureFamily AlgebraicComplex)
    {n m : ℕ} (hn : n=m) (h : NetworkRealizable F (equality n)) :
    NetworkRealizable F (equality m) := by
  subst m
  exact h

/-- The exact complementary four-port graph uses two copies of Eq_k and
the k−2 original native-X edges. -/
theorem complementary_realizable (F : SignatureFamily AlgebraicComplex)
    (k : ℕ) (hk : 3 ≤ k) (heq : NetworkRealizable F (equality k)) :
    NetworkRealizable F complementaryE := by
  let i : Fin k := ⟨0,by omega⟩
  let j : Fin k := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have hh := congrArg Fin.val h; simp [i,j] at hh
  let G := (gramFinite i j hij (equality (K := AlgebraicComplex) k)).toNetwork
  have hG : G.NativeX := by intro e; rfl
  have hv : ∀ v, NetworkRealizable F (G.vertex v) := fun _ => heq
  have h := NetworkRealizable.substitute G hG hv
  have hge : equality (K := AlgebraicComplex) k = generalizedEquality 1 1 := by
    funext x
    simp only [equality_eq,generalizedEquality]
  have hd : G.denote = complementaryE := by
    rw [gramFinite_denote,hge,generalizedEquality_gram_formula hk]
    simp
  exact hd ▸ h

namespace Merge

abbrev Boundary (r s : ℕ) := Fin 2 ⊕ (Fin r ⊕ Fin s)

def boundaryEquiv (r s : ℕ) : Boundary r s ≃ Fin (2 + (r+s)) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

abbrev arity (r s : ℕ) : Option Bool → ℕ
  | none => 4
  | some false => r+1
  | some true => s+1

def ports (r s : ℕ) : (Σ v : Option Bool, Fin (arity r s v)) ≃
    (Fin (2+(r+s)) ⊕ (Bool × Bool)) where
  toFun p := match p with
    | ⟨none,i⟩ => if i.val=0 then .inl (boundaryEquiv r s (.inl 0))
        else if i.val=1 then .inl (boundaryEquiv r s (.inl 1))
        else if i.val=2 then .inr (false,true) else .inr (true,true)
    | ⟨some false,i⟩ => Fin.cases (.inr (false,false))
        (fun j => .inl (boundaryEquiv r s (.inr (.inl j)))) i
    | ⟨some true,i⟩ => Fin.cases (.inr (true,false))
        (fun j => .inl (boundaryEquiv r s (.inr (.inr j)))) i
  invFun p := match p with
    | .inl i => match (boundaryEquiv r s).symm i with
      | .inl j => if j=0 then ⟨none,0⟩ else ⟨none,1⟩
      | .inr (.inl j) => ⟨some false,j.succ⟩
      | .inr (.inr j) => ⟨some true,j.succ⟩
    | .inr (false,false) => ⟨some false,0⟩
    | .inr (true,false) => ⟨some true,0⟩
    | .inr (false,true) => ⟨none,2⟩
    | .inr (true,true) => ⟨none,3⟩
  left_inv := by
    rintro ⟨v,i⟩
    cases v with
    | none => fin_cases i <;> simp [Equiv.symm_apply_apply] <;> rfl
    | some b =>
      cases b <;> refine Fin.cases ?_ (fun j => ?_) i
      all_goals simp [Equiv.symm_apply_apply]
  right_inv := by
    rintro (i | ⟨a,b⟩)
    · obtain ⟨j,rfl⟩ := (boundaryEquiv r s).surjective i
      cases j with
      | inl j => fin_cases j <;> simp [Equiv.symm_apply_apply]
      | inr j => cases j <;> simp [Equiv.symm_apply_apply]
    · cases a <;> cases b <;> rfl

def finite (r s : ℕ) : FiniteNetwork AlgebraicComplex (Option Bool) Bool (2+(r+s)) where
  arity := arity r s
  ports := ports r s
  vertex v := match v with
    | none => complementaryE
    | some false => equality (r+1)
    | some true => equality (s+1)
  edge _ := Signature.disequality

def boundaryWord (r s : ℕ) (x : Fin (2+(r+s)) → Bool) : Boundary r s → Bool :=
  fun i => x (boundaryEquiv r s i)

def leftWord (r s : ℕ) (x : Fin (2+(r+s)) → Bool) (b : Bool) : Fin (r+1) → Bool :=
  Fin.cons b (fun i => boundaryWord r s x (.inr (.inl i)))

def rightWord (r s : ℕ) (x : Fin (2+(r+s)) → Bool) (b : Bool) : Fin (s+1) → Bool :=
  Fin.cons b (fun i => boundaryWord r s x (.inr (.inr i)))

def middleWord (r s : ℕ) (x : Fin (2+(r+s)) → Bool) (a b : Bool) : Fin 4 → Bool :=
  ![boundaryWord r s x (.inl 0),boundaryWord r s x (.inl 1),!a,!b]

theorem finite_denote_formula (r s : ℕ) (x : Fin (2+(r+s)) → Bool) :
    (finite r s).denote x = ∑ a : Bool, ∑ b : Bool,
      complementaryE (middleWord r s x a b) *
        (equality (r+1) (leftWord r s x a) * equality (s+1) (rightWord r s x b)) := by
  classical
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  trans (∑ z : Bool → Bool, ∏ v : Option Bool, (finite r s).vertex v
    (fun i => Sum.elim x (fun q : Bool × Bool => if q.2 then !(z q.1) else z q.1)
      ((ports r s) ⟨v,i⟩)))
  · apply Finset.sum_congr (by ext; simp)
    intro z _
    rfl
  · rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp
      (fun z : Bool → Bool => ∏ v : Option Bool, (finite r s).vertex v
        (fun i => Sum.elim x (fun q : Bool × Bool => if q.2 then !(z q.1) else z q.1)
          ((ports r s) ⟨v,i⟩)))]
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [Fintype.prod_option,Fintype.prod_bool]
    have hm : (fun i : Fin 4 => Sum.elim x
        (fun q : Bool × Bool => if q.2 then !((Equiv.boolArrowEquivProd Bool).symm (a,b) q.1)
          else (Equiv.boolArrowEquivProd Bool).symm (a,b) q.1)
        ((ports r s) ⟨none,i⟩)) = middleWord r s x a b := by
      funext i
      fin_cases i <;> rfl
    have hl : (fun i : Fin (r+1) => Sum.elim x
        (fun q : Bool × Bool => if q.2 then !((Equiv.boolArrowEquivProd Bool).symm (a,b) q.1)
          else (Equiv.boolArrowEquivProd Bool).symm (a,b) q.1)
        ((ports r s) ⟨some false,i⟩)) = leftWord r s x a := by
      funext i
      refine Fin.cases rfl (fun j => rfl) i
    have hr : (fun i : Fin (s+1) => Sum.elim x
        (fun q : Bool × Bool => if q.2 then !((Equiv.boolArrowEquivProd Bool).symm (a,b) q.1)
          else (Equiv.boolArrowEquivProd Bool).symm (a,b) q.1)
        ((ports r s) ⟨some true,i⟩)) = rightWord r s x b := by
      funext i
      refine Fin.cases rfl (fun j => rfl) i
    dsimp only [finite]
    change complementaryE _ * (equality (s+1) _ * equality (r+1) _) = _
    rw [hm,hl,hr]
    ring

theorem leftWord_constant_iff (r s : ℕ) (x : Fin (2+(r+s)) → Bool) (a b : Bool) :
    leftWord r s x a = (fun _ => b) ↔
      a=b ∧ ∀ i : Fin r, boundaryWord r s x (.inr (.inl i))=b := by
  simp [funext_iff,leftWord,Fin.forall_fin_succ]

theorem rightWord_constant_iff (r s : ℕ) (x : Fin (2+(r+s)) → Bool) (a b : Bool) :
    rightWord r s x a = (fun _ => b) ↔
      a=b ∧ ∀ i : Fin s, boundaryWord r s x (.inr (.inr i))=b := by
  simp [funext_iff,rightWord,Fin.forall_fin_succ]

theorem constant_iff (r s : ℕ) (x : Fin (2+(r+s)) → Bool) (b : Bool) :
    x = (fun _ => b) ↔
      boundaryWord r s x (.inl 0)=b ∧ boundaryWord r s x (.inl 1)=b ∧
      (∀ i : Fin r, boundaryWord r s x (.inr (.inl i))=b) ∧
      (∀ i : Fin s, boundaryWord r s x (.inr (.inr i))=b) := by
  constructor
  · rintro rfl
    simp [boundaryWord]
  · rintro ⟨h0,h1,hl,hr⟩
    funext i
    obtain ⟨j,rfl⟩ := (boundaryEquiv r s).surjective i
    cases j with
    | inl j => fin_cases j; exact h0; exact h1
    | inr j => cases j with
      | inl j => exact hl j
      | inr j => exact hr j

/-- The merger has coefficient one at both constant words and zero at all
other words, with its two new boundary ports retained literally. -/
theorem finite_denote (r s : ℕ) : (finite r s).denote = equality (2+(r+s)) := by
  funext x
  rw [finite_denote_formula,equality_eq]
  simp only [Fintype.sum_bool,equality_eq,leftWord_constant_iff,rightWord_constant_iff,
    constant_iff]
  cases h0 : boundaryWord r s x (.inl 0) <;>
    cases h1 : boundaryWord r s x (.inl 1) <;>
      simp [middleWord,complementaryE,h0,h1,←ite_and,and_comm]

end Merge

/-- The complementary E4 graph joins two positive equality blocks. All
internal wires are X; neither an identity binary nor a unary is supplied. -/
theorem equality_merge_realizable (F : SignatureFamily AlgebraicComplex)
    (r s : ℕ) (hr : NetworkRealizable F (equality (r+1)))
    (hs : NetworkRealizable F (equality (s+1)))
    (hE : NetworkRealizable F complementaryE) :
    NetworkRealizable F (equality ((r+1)+(s+1))) := by
  let G := (Merge.finite r s).toNetwork
  have hX : G.NativeX := by intro e; rfl
  have hv : ∀ v, NetworkRealizable F (G.vertex v) := by
    intro v
    change NetworkRealizable F ((Merge.finite r s).vertex
      ((Fintype.equivFin (Option Bool)).symm v))
    cases (Fintype.equivFin (Option Bool)).symm v with
    | none => exact hE
    | some b => cases b; exact hr; exact hs
  have h := NetworkRealizable.substitute G hX hv
  have hd : G.denote = equality (2+(r+s)) := by
    rw [FiniteNetwork.denote_toNetwork]
    exact Merge.finite_denote r s
  rw [hd] at h
  have he : 2+(r+s)=(r+1)+(s+1) := by omega
  have hout := h.reindex (finCongr he)
  simpa only [equality_reindex] using hout

namespace Closed

def ports (k : ℕ) : (Σ _ : Bool, Fin k) ≃ (Fin 0 ⊕ (Fin k × Bool)) where
  toFun p := .inr (p.2,p.1)
  invFun
    | .inl i => Fin.elim0 i
    | .inr (i,b) => ⟨b,i⟩
  left_inv := by rintro ⟨b,i⟩; rfl
  right_inv := by rintro (i | ⟨i,b⟩); exact Fin.elim0 i; rfl

def finite (k : ℕ) : FiniteNetwork AlgebraicComplex Bool (Fin k) 0 where
  arity _ := k
  ports := ports k
  vertex _ := equality k
  edge _ := Signature.disequality

theorem equality_square (k : ℕ) (hk : 0 < k) (x : Fin k → Bool) :
    equality (K := AlgebraicComplex) k x * equality k x = equality k x := by
  have hne : (fun _ : Fin k => false) ≠ (fun _ => true) := by
    intro h
    exact Bool.false_ne_true (congrFun h ⟨0,hk⟩)
  rw [equality_eq]
  by_cases h0 : x=(fun _ => false)
  · subst x
    simp [hne]
  · by_cases h1 : x=(fun _ => true) <;> simp [h0,h1,Ne.symm hne]

theorem finite_denote (k : ℕ) (hk : 0 < k) : (finite k).denote = equality 0 := by
  classical
  letI : DecidableEq (Fin k) := Classical.decEq (Fin k)
  funext x
  rw [FiniteNetwork.denote_nativeX _ (fun _ => rfl)]
  change (∑ z : Fin k → Bool, ∏ v : Bool,
    equality (K := AlgebraicComplex) k (fun i => if v then !(z i) else z i)) = _
  simp only [Fintype.prod_bool,↓reduceIte]
  change (∑ z : Fin k → Bool, equality (K := AlgebraicComplex) k (fun i => !(z i)) *
    equality k z) = equality 0 x
  rw [equality_zero]
  simp_rw [equality_complement,equality_square k hk]
  simp only [equality_eq,Finset.sum_add_distrib]
  norm_num

end Closed

/-- A degree-zero CSP variable contributes two. The actual graph is two
Eq_k copies joined at every corresponding port through k native-X edges. -/
theorem equality_zero_realizable (F : SignatureFamily AlgebraicComplex)
    (k : ℕ) (hk : 0 < k) (heq : NetworkRealizable F (equality k)) :
    NetworkRealizable F (equality 0) := by
  let G := (Closed.finite k).toNetwork
  have hX : G.NativeX := by intro e; rfl
  have h := NetworkRealizable.substitute G hX (fun _ => heq)
  have hd : G.denote=equality 0 := by
    rw [FiniteNetwork.denote_toNetwork]
    exact Closed.finite_denote k hk
  exact hd ▸ h

/-- Every nonnegative multiple of the fixed arity has a genuine native-X
graph over exactly the supplied resource family, including the nullary two. -/
theorem equality_multiple_realizable (F : SignatureFamily AlgebraicComplex)
    (k : ℕ) (hk : 3 ≤ k) (heq : NetworkRealizable F (equality k)) (m : ℕ) :
    NetworkRealizable F (equality (m*k)) := by
  have hE := complementary_realizable F k hk heq
  induction m with
  | zero =>
    exact equality_realizable_congr F (Nat.zero_mul k).symm
      (equality_zero_realizable F k (by omega) heq)
  | succ m ih =>
    cases m with
    | zero => exact equality_realizable_congr F (Nat.one_mul k).symm heq
    | succ m =>
      have hr : 0 < (m+1)*k := by positivity
      have h := equality_merge_realizable F ((m+1)*k-1) (k-1)
        (equality_realizable_congr F (Nat.sub_add_cancel (by omega)).symm ih)
        (equality_realizable_congr F (Nat.sub_add_cancel (by omega)).symm heq) hE
      have hdegree : ((m+1)*k-1+1)+(k-1+1)=(m+1+1)*k := by
        rw [Nat.sub_add_cancel (by omega),Nat.sub_add_cancel (by omega)]
        ring
      exact equality_realizable_congr F hdegree h

namespace ComplementLoop

/-- Leave E4 ports 1,3 in order and join ports 0,2 through one actual X. -/
def ports : Fin 4 ≃ (Fin 2 ⊕ Bool) where
  toFun i := if i.val=0 then .inr false else if i.val=1 then .inl 0
    else if i.val=2 then .inr true else .inl 1
  invFun
    | .inl i => if i=0 then 1 else 3
    | .inr false => 0
    | .inr true => 2
  left_inv := by intro i; fin_cases i <;> simp <;> rfl
  right_inv := by
    rintro (i | b)
    · fin_cases i <;> rfl
    · cases b <;> rfl

theorem contraction : Tensor.contractX (Tensor.reindex ports complementaryE) =
    (fun x : Fin 2 → Bool => Signature.disequality (x 0) (x 1)) := by
  funext x
  simp only [Tensor.contractX,Fintype.sum_bool,Tensor.reindex_apply]
  have h (b : Bool) : (fun i => Sum.elim x (fun c : Bool => if c then !b else b) (ports i)) =
      ![b,x 0,!b,x 1] := by
    funext i
    fin_cases i <;> rfl
  rw [h,h]
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [complementaryE,Signature.disequality,h0,h1]

end ComplementLoop

/-- A binary X vertex is itself a physical consequence of the supplied
Eq_k graph, rather than an extra constraint assumed by the CSP compiler. -/
theorem disequality_realizable (F : SignatureFamily AlgebraicComplex)
    (k : ℕ) (hk : 3 ≤ k) (heq : NetworkRealizable F (equality k)) :
    NetworkRealizable F (fun x : Fin 2 → Bool => Signature.disequality (x 0) (x 1)) := by
  have hE := complementary_realizable F k hk heq
  have h := (hE.reindex ComplementLoop.ports).selfLoop
  exact ComplementLoop.contraction ▸ h

end
end Paper2.DegreeCSP

