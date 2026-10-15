import Paper2.DegreeCSP.EqualityMultiples

/-! A deterministic path layout for equality macros. Main Eq_k vertices
occupy the first m positions. The following connector pair A_t,B_t occupies
positions m+2t,m+2t+1, and edge (t,j) occupies position t*k+j. No runtime
choice of a graph witness occurs in these definitions. -/
namespace Paper2.DegreeCSP.EqualityTemplates
open Paper2.ExactInput Paper2.Tractable
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

abbrev Vertices (m : ℕ) := Fin m ⊕ (Fin (m-1) × Bool)
abbrev Boundary (m k : ℕ) := Fin m × Fin k
abbrev Edges (m k : ℕ) := Fin (m-1) × Fin k

def vertexEquiv (m : ℕ) : Vertices m ≃ Fin (m+(m-1)*2) :=
  (Equiv.sumCongr (Equiv.refl _)
    ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv)).trans finSumFinEquiv

@[simp] theorem vertexEquiv_main_val (m : ℕ) (t : Fin m) :
    (vertexEquiv m (.inl t)).val=t.val := rfl

theorem vertexEquiv_connector_val (m : ℕ) (t : Fin (m-1)) (b : Bool) :
    (vertexEquiv m (.inr (t,b))).val=m+2*t.val+(if b then 1 else 0) := by
  cases b <;> simp [vertexEquiv,finProdFinEquiv,finTwoEquiv] <;> omega

abbrev boundaryEquiv (m k : ℕ) : Boundary m k ≃ Fin (m*k) := finProdFinEquiv
abbrev edgeEquiv (m k : ℕ) : Edges m k ≃ Fin ((m-1)*k) := finProdFinEquiv

abbrev zero (k : ℕ) (hk : 3 ≤ k) : Fin k := ⟨0,by omega⟩
abbrev one (k : ℕ) (hk : 3 ≤ k) : Fin k := ⟨1,by omega⟩
abbrev two (k : ℕ) (hk : 3 ≤ k) : Fin k := ⟨2,by omega⟩

def base {m : ℕ} (t : Fin (m-1)) : Fin m := ⟨t.val,by have := t.isLt; omega⟩
def next {m : ℕ} (t : Fin (m-1)) : Fin m := ⟨t.val+1,by have := t.isLt; omega⟩
def prev {m : ℕ} (t : Fin m) (ht : 0 < t.val) : Fin (m-1) := ⟨t.val-1,by have := t.isLt; omega⟩
def current {m : ℕ} (t : Fin m) (ht : t.val < m-1) : Fin (m-1) := ⟨t.val,ht⟩

@[simp] theorem base_prev {m : ℕ} (t : Fin m) (ht : 0 < t.val) :
    next (prev t ht)=t := by apply Fin.ext; simp [next,prev]; omega
@[simp] theorem prev_next {m : ℕ} (t : Fin (m-1)) (ht : 0 < (next t).val) :
    prev (next t) ht=t := by apply Fin.ext; simp [prev,next]
@[simp] theorem base_current {m : ℕ} (t : Fin m) (ht : t.val < m-1) :
    base (current t ht)=t := by rfl
@[simp] theorem current_base {m : ℕ} (t : Fin (m-1)) (ht : (base t).val < m-1) :
    current (base t) ht=t := by rfl

def namedPorts (m k : ℕ) (hk : 3 ≤ k) :
    (Vertices m × Fin k) ≃ (Boundary m k ⊕ (Edges m k × Bool)) where
  toFun p := match p.1 with
    | .inl t => if h0 : p.2.val=0 ∧ 0<t.val then .inr ((prev t h0.2,one k hk),false)
        else if h1 : p.2.val=1 ∧ t.val<m-1 then .inr ((current t h1.2,zero k hk),false)
        else .inl (t,p.2)
    | .inr (t,false) => if p.2.val=0 then .inl (base t,one k hk)
        else if p.2.val=1 then .inl (next t,zero k hk) else .inr ((t,p.2),false)
    | .inr (t,true) => .inr ((t,p.2),true)
  invFun p := match p with
    | .inl (t,j) => if h0 : j.val=0 ∧ 0<t.val then (.inr (prev t h0.2,false),one k hk)
        else if h1 : j.val=1 ∧ t.val<m-1 then (.inr (current t h1.2,false),zero k hk)
        else (.inl t,j)
    | .inr ((t,j),false) => if j.val=0 then (.inl (base t),one k hk)
        else if j.val=1 then (.inl (next t),zero k hk) else (.inr (t,false),j)
    | .inr ((t,j),true) => (.inr (t,true),j)
  left_inv := by
    rintro ⟨v,j⟩
    cases v with
    | inl t =>
      dsimp only
      split_ifs with h0 h1
      · simp [one,next,prev]
        constructor
        · apply Fin.ext
          simp
          omega
        · apply Fin.ext; exact h0.1.symm
      · simp [zero,base,current]
        apply Fin.ext
        exact h1.1.symm
      · simp only <;> (split_ifs <;> simp_all)
    | inr p =>
      rcases p with ⟨t,b⟩
      cases b
      · dsimp only
        split_ifs with h0 h1
        · simp [base,one,zero,current]
          apply Fin.ext
          exact h0.symm
        · simp [next,zero,one,prev]
          apply Fin.ext
          exact h1.symm
        · simp only <;> (split_ifs <;> simp_all)
      · rfl
  right_inv := by
    rintro (⟨t,j⟩ | ⟨⟨t,j⟩,b⟩)
    · dsimp only
      split_ifs with h0 h1
      · simp [one,zero,next,prev]
        constructor
        · apply Fin.ext; simp [next,prev]; omega
        · apply Fin.ext; exact h0.1.symm
      · simp [zero,one,base,current]
        apply Fin.ext
        exact h1.1.symm
      · simp only <;> (split_ifs <;> simp_all)
    · cases b
      · dsimp only
        split_ifs with h0 h1
        · simp [base,one,zero,current,t.isLt]
          apply Fin.ext
          exact h0.symm
        · simp [next,zero,one,prev]
          apply Fin.ext
          exact h1.symm
        · simp only <;> (split_ifs <;> simp_all)
      · rfl

def positivePorts (m k : ℕ) (hk : 3 ≤ k) :
    (Σ _ : Fin (m+(m-1)*2),Fin k) ≃ (Fin (m*k) ⊕ (Fin ((m-1)*k) × Bool)) :=
  (Equiv.sigmaEquivProd _ _).trans
    ((Equiv.prodCongr (vertexEquiv m).symm (Equiv.refl _)).trans
      ((namedPorts m k hk).trans (Equiv.sumCongr (boundaryEquiv m k)
        (Equiv.prodCongr (edgeEquiv m k) (Equiv.refl _)))))

theorem positivePorts_named (m k : ℕ) (hk : 3 ≤ k) (v : Vertices m) (j : Fin k) :
    positivePorts m k hk ⟨vertexEquiv m v,j⟩ =
      Sum.map (boundaryEquiv m k) (fun p => (edgeEquiv m k p.1,p.2))
        (namedPorts m k hk (v,j)) := by
  simp [positivePorts, Prod.map]
  rfl

def positive (m k : ℕ) (hk : 3 ≤ k) : Network AlgebraicComplex (m*k) where
  shape := {
    vertices := m+(m-1)*2
    arity _ := k
    edges := (m-1)*k
    ports := positivePorts m k hk }
  vertex _ := equality k
  edge _ := Signature.disequality

@[simp] theorem positive_vertices (m k : ℕ) (hk : 3 ≤ k) :
    (positive m k hk).shape.vertices=m+(m-1)*2 := rfl
@[simp] theorem positive_edges (m k : ℕ) (hk : 3 ≤ k) :
    (positive m k hk).shape.edges=(m-1)*k := rfl
theorem positive_vertices_linear (m k : ℕ) (hk : 3 ≤ k) (hm : 0<m) :
    (positive m k hk).shape.vertices=3*m-2 := by simp only [positive_vertices]; omega
theorem positive_nativeX (m k : ℕ) (hk : 3 ≤ k) : (positive m k hk).NativeX := fun _ => rfl
theorem positive_vertex (m k : ℕ) (hk : 3 ≤ k) (v : Fin (m+(m-1)*2)) :
    (positive m k hk).vertex v=equality k := rfl

def nullaryPorts (k : ℕ) : (Σ _ : Fin 2,Fin k) ≃ (Fin 0 ⊕ (Fin k × Bool)) where
  toFun p := .inr (p.2,finTwoEquiv p.1)
  invFun
    | .inl i => Fin.elim0 i
    | .inr (j,b) => ⟨finTwoEquiv.symm b,j⟩
  left_inv := by rintro ⟨v,j⟩; simp
  right_inv := by
    rintro (i | ⟨j,b⟩)
    · exact Fin.elim0 i
    · simp

/-- The two rows have the literal fixed order: false edge-ends first,
then true edge-ends. Its closed value is two for every positive k. -/
def nullary (k : ℕ) : Network AlgebraicComplex 0 where
  shape := { vertices := 2, arity _ := k, edges := k, ports := nullaryPorts k }
  vertex _ := equality k
  edge _ := Signature.disequality

theorem nullary_nativeX (k : ℕ) : (nullary k).NativeX := fun _ => rfl
theorem nullary_vertex (k : ℕ) (v : Fin 2) : (nullary k).vertex v=equality k := rfl
@[simp] theorem nullary_port_zero (k : ℕ) (j : Fin k) :
    (nullary k).shape.ports ⟨(0 : Fin 2),j⟩=.inr (j,false) := rfl
@[simp] theorem nullary_port_one (k : ℕ) (j : Fin k) :
    (nullary k).shape.ports ⟨(1 : Fin 2),j⟩=.inr (j,true) := rfl
@[simp] theorem nullary_vertices (k : ℕ) : (nullary k).shape.vertices=2 := rfl
@[simp] theorem nullary_edges (k : ℕ) : (nullary k).shape.edges=k := rfl

end
end Paper2.DegreeCSP.EqualityTemplates
