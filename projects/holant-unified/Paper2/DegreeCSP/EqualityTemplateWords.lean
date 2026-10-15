import Paper2.DegreeCSP.EqualityTemplates

/-! Exact local words in the deterministic equality path. Every main row
retains port 2, which fixes its common bit. The connector rows identify the
bits of neighboring main rows and force every oriented edge assignment. -/
namespace Paper2.DegreeCSP.EqualityTemplates
open Paper2.ExactInput Paper2.Tractable
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

def mainWord {m k : ℕ} (hk : 3 ≤ k) (x : Boundary m k → Bool)
    (z : Edges m k → Bool) (t : Fin m) (j : Fin k) : Bool :=
  if h0 : j.val=0 ∧ 0<t.val then z (prev t h0.2,one k hk)
  else if h1 : j.val=1 ∧ t.val<m-1 then z (current t h1.2,zero k hk) else x (t,j)

def aWord {m k : ℕ} (hk : 3 ≤ k) (x : Boundary m k → Bool)
    (z : Edges m k → Bool) (t : Fin (m-1)) (j : Fin k) : Bool :=
  if j.val=0 then x (base t,one k hk)
  else if j.val=1 then x (next t,zero k hk) else z (t,j)

def bWord {m k : ℕ} (z : Edges m k → Bool) (t : Fin (m-1)) (j : Fin k) : Bool := !(z (t,j))

def row {m k : ℕ} (hk : 3 ≤ k) (x : Boundary m k → Bool)
    (z : Edges m k → Bool) (v : Vertices m) : Fin k → Bool :=
  match v with
  | .inl t => mainWord hk x z t
  | .inr (t,false) => aWord hk x z t
  | .inr (t,true) => bWord z t

def pathWeight {m k : ℕ} (hk : 3 ≤ k) (x : Boundary m k → Bool)
    (z : Edges m k → Bool) : AlgebraicComplex := ∏ v : Vertices m, equality k (row hk x z v)

theorem equality_nonzero_constant (k : ℕ) (x : Fin k → Bool)
    (hx : equality (K := AlgebraicComplex) k x ≠ 0) : ∃ b : Bool, ∀ j, x j=b := by
  classical
  by_cases h0 : x=(fun _ => false)
  · exact ⟨false,fun j => congrFun h0 j⟩
  · have h1 : x=(fun _ => true) := by
      by_contra h1
      apply hx
      simp [equality_eq,h0,h1]
    exact ⟨true,fun j => congrFun h1 j⟩

theorem equality_pair_of_nonzero (k : ℕ) (x : Fin k → Bool)
    (hx : equality (K := AlgebraicComplex) k x ≠ 0) (i j : Fin k) : x i=x j := by
  obtain ⟨b,hb⟩ := equality_nonzero_constant k x hx
  rw [hb i,hb j]

theorem equality_constant (k : ℕ) (hk : 0<k) (b : Bool) :
    equality (K := AlgebraicComplex) k (fun _ => b)=1 := by
  have hn : (fun _ : Fin k => false) ≠ (fun _ => true) := by
    intro h
    exact Bool.false_ne_true (congrFun h ⟨0,hk⟩)
  cases b <;> simp [equality_eq,hn,Ne.symm hn]

@[simp] theorem mainWord_two {m k : ℕ} (hk : 3 ≤ k) (x : Boundary m k → Bool)
    (z : Edges m k → Bool) (t : Fin m) : mainWord hk x z t (two k hk)=x (t,two k hk) := by
  simp [mainWord]

@[simp] theorem aWord_zero {m k : ℕ} (hk : 3 ≤ k) (x : Boundary m k → Bool)
    (z : Edges m k → Bool) (t : Fin (m-1)) : aWord hk x z t (zero k hk)=x (base t,one k hk) := by
  simp [aWord]

@[simp] theorem aWord_one {m k : ℕ} (hk : 3 ≤ k) (x : Boundary m k → Bool)
    (z : Edges m k → Bool) (t : Fin (m-1)) : aWord hk x z t (one k hk)=x (next t,zero k hk) := by
  simp [aWord]

@[simp] theorem aWord_two {m k : ℕ} (hk : 3 ≤ k) (x : Boundary m k → Bool)
    (z : Edges m k → Bool) (t : Fin (m-1)) : aWord hk x z t (two k hk)=z (t,two k hk) := by
  simp [aWord]

@[simp] theorem mainWord_base_one {m k : ℕ} (hk : 3 ≤ k) (x : Boundary m k → Bool)
    (z : Edges m k → Bool) (t : Fin (m-1)) : mainWord hk x z (base t) (one k hk)=z (t,zero k hk) := by
  simp [mainWord,base,current,t.isLt]

@[simp] theorem mainWord_next_zero {m k : ℕ} (hk : 3 ≤ k) (x : Boundary m k → Bool)
    (z : Edges m k → Bool) (t : Fin (m-1)) : mainWord hk x z (next t) (zero k hk)=z (t,one k hk) := by
  simp [mainWord,next,prev]

/-- Nonzero product forces the single common external bit and the unique
internal edge assignment; the argument is valid for arbitrary algebraic
complex coefficients because every row is a literal equality indicator. -/
theorem pathWeight_nonzero {m k : ℕ} (hk : 3 ≤ k) (hm : 0<m)
    (x : Boundary m k → Bool) (z : Edges m k → Bool)
    (hw : pathWeight hk x z ≠ 0) :
    (∀ p, x p=x (⟨0,hm⟩,two k hk)) ∧ (∀ e, z e=x (⟨0,hm⟩,two k hk)) := by
  classical
  have hv : ∀ v : Vertices m, equality (K := AlgebraicComplex) k (row hk x z v) ≠ 0 :=
    fun v => (Finset.prod_ne_zero_iff.mp hw) v (Finset.mem_univ v)
  have hs : ∀ v : Vertices m, ∀ i j, row hk x z v i=row hk x z v j :=
    fun v i j => equality_pair_of_nonzero k _ (hv v) i j
  have hz : ∀ t : Fin (m-1), ∀ j, z (t,j)=z (t,zero k hk) := by
    intro t j
    have h := hs (.inr (t,true)) j (zero k hk)
    change (!(z (t,j))) = !(z (t,zero k hk)) at h
    cases h1 : z (t,j) <;> cases h2 : z (t,zero k hk) <;> simp_all
  have hb : ∀ t : Fin (m-1), z (t,zero k hk)=x (base t,two k hk) := by
    intro t
    simpa only [row,mainWord_base_one,mainWord_two] using hs (.inl (base t)) (one k hk) (two k hk)
  have hn : ∀ t : Fin (m-1), z (t,one k hk)=x (next t,two k hk) := by
    intro t
    simpa only [row,mainWord_next_zero,mainWord_two] using hs (.inl (next t)) (zero k hk) (two k hk)
  have hadj : ∀ t : Fin (m-1), x (base t,two k hk)=x (next t,two k hk) := by
    intro t
    exact (hb t).symm.trans ((hz t (one k hk)).symm.trans (hn t))
  have hall : ∀ a : ℕ, ∀ ha : a<m, x (⟨a,ha⟩,two k hk)=x (⟨0,hm⟩,two k hk) := by
    intro a
    induction a with
    | zero => intro ha; rfl
    | succ a ih =>
      intro ha
      let t : Fin (m-1) := ⟨a,by omega⟩
      exact (hadj t).symm.trans (ih (by omega))
  have hmain : ∀ t : Fin m, x (t,two k hk)=x (⟨0,hm⟩,two k hk) :=
    fun t => hall t.val t.isLt
  have hedge : ∀ e, z e=x (⟨0,hm⟩,two k hk) := by
    rintro ⟨t,j⟩
    exact (hz t j).trans ((hb t).trans (hmain (base t)))
  refine ⟨?_,hedge⟩
  rintro ⟨t,j⟩
  by_cases h0 : j.val=0 ∧ 0<t.val
  · have hj : j=zero k hk := Fin.ext h0.1
    subst j
    have h := hs (.inr (prev t h0.2,false)) (one k hk) (two k hk)
    simp only [row,aWord_one,aWord_two,base_prev] at h
    exact h.trans (hedge _)
  · by_cases h1 : j.val=1 ∧ t.val<m-1
    · have hj : j=one k hk := Fin.ext h1.1
      subst j
      have h := hs (.inr (current t h1.2,false)) (zero k hk) (two k hk)
      simp only [row,aWord_zero,aWord_two,base_current] at h
      exact h.trans (hedge _)
    · have h := hs (.inl t) j (two k hk)
      simp only [row,mainWord_two,mainWord,dif_neg h0,dif_neg h1] at h
      exact h.trans (hmain t)

theorem pathWeight_constant {m k : ℕ} (hk : 3 ≤ k)
    (x : Boundary m k → Bool) (z : Edges m k → Bool) (b : Bool)
    (hx : ∀ p, x p=b) (hz : ∀ e, z e=b) : pathWeight hk x z=1 := by
  have hr : ∀ v : Vertices m, row hk x z v =
      (fun _ => match v with | .inl _ => b | .inr (_,false) => b | .inr (_,true) => !b) := by
    intro v
    funext j
    cases v with
    | inl t => simp [row,mainWord,hx,hz]
    | inr p => rcases p with ⟨t,c⟩; cases c <;> simp [row,aWord,bWord,hx,hz]
  unfold pathWeight
  simp_rw [hr,equality_constant k (by omega)]
  simp

theorem pathWeight_formula {m k : ℕ} (hk : 3 ≤ k) (hm : 0<m)
    (x : Boundary m k → Bool) (z : Edges m k → Bool) : pathWeight hk x z =
    if (∀ p, x p=x (⟨0,hm⟩,two k hk)) ∧ (∀ e, z e=x (⟨0,hm⟩,two k hk)) then 1 else 0 := by
  classical
  by_cases h : (∀ p, x p=x (⟨0,hm⟩,two k hk)) ∧ (∀ e, z e=x (⟨0,hm⟩,two k hk))
  · rw [if_pos h]
    exact pathWeight_constant hk x z _ h.1 h.2
  · rw [if_neg h]
    by_contra hw
    exact h (pathWeight_nonzero hk hm x z hw)

end
end Paper2.DegreeCSP.EqualityTemplates
