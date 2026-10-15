import Paper2.DegreeCSP.Model

/-! The literal incidence network of a finite Boolean CSP. Constraint ports
keep their original order. Each separate scope position is one native X edge,
whose other end is a port of the variable's equality vertex. Global Boolean
complementation accounts for the orientation of these native X edges. -/
namespace Paper2.DegreeCSP
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def splitEnds (α : Type) : (α ⊕ α) ≃ (α × Bool) where
  toFun := Sum.elim (fun p => (p,false)) (fun p => (p,true))
  invFun p := if p.2 then .inr p.1 else .inl p.1
  left_inv := by rintro (p | p) <;> rfl
  right_inv := by rintro ⟨p,b⟩; cases b <;> rfl

def noBoundary (E : Type) : (E × Bool) ≃ (Fin 0 ⊕ (E × Bool)) where
  toFun := Sum.inr
  invFun := Sum.elim Fin.elim0 id
  left_inv _ := rfl
  right_inv := by rintro (i | p); exact Fin.elim0 i; rfl

namespace Instance
variable {K : Type} [CommSemiring K] (I : Instance K)

def incidenceArity : (Fin I.constraints ⊕ Fin I.variableCount) → ℕ :=
  Sum.elim I.arity I.degree

def incidencePorts : (Σ v, Fin (I.incidenceArity v)) ≃
    (Fin 0 ⊕ (I.Occurrence × Bool)) :=
  (Equiv.sumSigmaDistrib (fun v => Fin (I.incidenceArity v))).trans
    ((Equiv.sumCongr (Equiv.refl _) I.variablePorts).trans
      ((splitEnds I.Occurrence).trans (noBoundary I.Occurrence)))

def incidence : FiniteNetwork K (Fin I.constraints ⊕ Fin I.variableCount) I.Occurrence 0 where
  arity := I.incidenceArity
  ports := I.incidencePorts
  vertex v := match v with
    | .inl c => I.table c
    | .inr v => equality (I.degree v)
  edge _ := Signature.disequality

omit [CommSemiring K] in
@[simp] theorem incidencePorts_constraint (c : Fin I.constraints) (j : Fin (I.arity c)) :
    I.incidencePorts ⟨.inl c,j⟩ = .inr (⟨c,j⟩,false) := rfl

omit [CommSemiring K] in
@[simp] theorem incidencePorts_variable (v : Fin I.variableCount) (j : Fin (I.degree v)) :
    I.incidencePorts ⟨.inr v,j⟩ = .inr (I.variablePorts ⟨v,j⟩,true) := rfl

theorem incidence_nativeX : ∀ e, I.incidence.edge e = Signature.disequality := fun _ => rfl

theorem incidence_denote_sum : I.incidence.denote Fin.elim0 =
    ∑ z : I.Occurrence → Bool, I.weight z *
      ∏ v : Fin I.variableCount,
        equality (I.degree v) (fun j => !(z (I.variablePorts ⟨v,j⟩))) := by
  rw [FiniteNetwork.denote_nativeX _ I.incidence_nativeX]
  apply Finset.sum_congr (by ext z; simp)
  intro z _
  rw [Fintype.prod_sum_type]
  rfl

/-- After choosing one variable bit, every occurrence has exactly its
opposite bit on the constraint end of its native X edge. -/
theorem incidence_guard (z : I.Occurrence → Bool) (x : Fin I.variableCount → Bool) :
    (∏ v : Fin I.variableCount, ∏ j : Fin (I.degree v),
      if Bool.not (z (I.variablePorts ⟨v,j⟩)) = x v then (1 : K) else 0) =
      if z = (fun p => !(x (I.route p))) then 1 else 0 := by
  classical
  rw [← Fintype.prod_sigma' (fun v (j : Fin (I.degree v)) =>
    if Bool.not (z (I.variablePorts ⟨v,j⟩)) = x v then (1 : K) else 0)]
  have he : (∏ p : (Σ v, Fin (I.degree v)),
      if Bool.not (z (I.variablePorts p)) = x p.1 then (1 : K) else 0) =
      ∏ p : I.Occurrence, if Bool.not (z p) = x (I.route p) then 1 else 0 := by
    apply Fintype.prod_equiv I.variablePorts
    intro p
    rw [I.variablePorts_route p.1 p.2]
  rw [he]
  have hb : (∀ p, Bool.not (z p) = x (I.route p)) ↔ z = (fun p => !(x (I.route p))) := by
    constructor
    · intro h
      funext p
      have hh := h p
      cases hz : z p <;> cases hx : x (I.route p) <;> simp_all
    · rintro rfl p
      simp
  simp only [Fintype.prod_boole,hb]

def complementAssignment : (Fin I.variableCount → Bool) ≃ (Fin I.variableCount → Bool) where
  toFun x v := !(x v)
  invFun x v := !(x v)
  left_inv := by intro x; funext v; simp
  right_inv := by intro x; funext v; simp

/-- Exact value preservation includes arbitrary repeated scopes, empty
constraints, and variables with degree zero. No surjectivity is imposed. -/
theorem incidence_partition : I.incidence.denote Fin.elim0 = I.partition := by
  classical
  rw [I.incidence_denote_sum]
  simp only [equality,Fintype.prod_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [I.incidence_guard,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold partition
  apply Fintype.sum_equiv I.complementAssignment
  intro x
  rfl

def incidenceNetwork : Network K 0 := I.incidence.toNetwork

theorem incidenceNetwork_partition : I.incidenceNetwork.denote Fin.elim0 = I.partition := by
  rw [incidenceNetwork,FiniteNetwork.denote_toNetwork]
  exact I.incidence_partition

theorem incidenceNetwork_nativeX : I.incidenceNetwork.NativeX := fun _ => rfl

end Instance
end
end Paper2.DegreeCSP
