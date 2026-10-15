import Paper2.DegreeCSP.RawData
import Paper2.DegreeCSP.Incidence

/-! The ordered raw incidence graph uses the stable occurrence ordinal read
from the input record. Its native-X partition identity is independent of any
choice of a finite enumeration for variables or ports. -/
namespace Paper2.DegreeCSP.Raw
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {s : ℕ} {a : ℕ → ℕ} {k : ℕ}
variable {K : Type} [CommSemiring K]
variable (G : (i : Fin s) → Signature K (a i.val)) (r : Input s a k)

abbrev IncidenceVertex := Fin r.val.factors.length ⊕ Fin r.val.variables

def incidenceArity : IncidenceVertex r → ℕ :=
  Sum.elim (fun c => (r.val.factors.get c).2.length) (fun i => degree r.val i.val)

def incidencePorts : (Σ v,Fin (incidenceArity r v)) ≃
    (Fin 0 ⊕ (Ports r.val × Bool)) :=
  (Equiv.sumSigmaDistrib (fun v => Fin (incidenceArity r v))).trans
    ((Equiv.sumCongr (Equiv.refl _) (grouping r).symm).trans
      ((splitEnds (Ports r.val)).trans (noBoundary (Ports r.val))))

def incidence : FiniteNetwork K (IncidenceVertex r) (Ports r.val) 0 where
  arity := incidenceArity r
  ports := incidencePorts r
  vertex v := match v with
    | .inl c => (toInstance G r).table c
    | .inr i => equality (degree r.val i.val)
  edge _ := Signature.disequality

omit [CommSemiring K] in
@[simp] theorem incidencePorts_constraint (c : Fin r.val.factors.length)
    (j : Fin (r.val.factors.get c).2.length) :
    incidencePorts r ⟨.inl c,j⟩ = .inr (⟨c,j⟩,false) := rfl

omit [CommSemiring K] in
@[simp] theorem incidencePorts_variable (i : Fin r.val.variables)
    (j : Fin (degree r.val i.val)) :
    incidencePorts r ⟨.inr i,j⟩ = .inr ((grouping r).symm ⟨i,j⟩,true) := rfl

theorem incidence_nativeX : ∀ e,(incidence G r).edge e = Signature.disequality := fun _ => rfl

theorem incidence_denote_sum : (incidence G r).denote Fin.elim0 =
    ∑ z : Ports r.val → Bool,factorWeight G r z *
      ∏ i : Fin r.val.variables,equality (degree r.val i.val)
        (fun j => !(z ((grouping r).symm ⟨i,j⟩))) := by
  rw [FiniteNetwork.denote_nativeX _ (incidence_nativeX G r)]
  apply Finset.sum_congr (by ext z; simp)
  intro z _
  rw [Fintype.prod_sum_type]
  rfl

theorem incidence_guard (z : Ports r.val → Bool) (x : Fin r.val.variables → Bool) :
    (∏ i : Fin r.val.variables,∏ j : Fin (degree r.val i.val),
      if Bool.not (z ((grouping r).symm ⟨i,j⟩)) = x i then (1 : K) else 0) =
      if z = (fun p => !(x (route r p))) then 1 else 0 := by
  classical
  rw [← Fintype.prod_sigma' (fun i (j : Fin (degree r.val i.val)) =>
    if Bool.not (z ((grouping r).symm ⟨i,j⟩)) = x i then (1 : K) else 0)]
  have he : (∏ p : (Σ i : Fin r.val.variables,Fin (degree r.val i.val)),
      if Bool.not (z ((grouping r).symm p)) = x p.1 then (1 : K) else 0) =
      ∏ p : Ports r.val,if Bool.not (z p) = x (route r p) then 1 else 0 := by
    apply Fintype.prod_equiv (grouping r).symm
    intro p
    have hp : route r ((grouping r).symm p) = p.1 := by
      rw [← grouping_variable r ((grouping r).symm p),(grouping r).apply_symm_apply]
    rw [hp]
  rw [he]
  have hb : (∀ p,Bool.not (z p) = x (route r p)) ↔ z = (fun p => !(x (route r p))) := by
    constructor
    · intro h
      funext p
      have hh := h p
      cases hz : z p <;> cases hx : x (route r p) <;> simp_all
    · rintro rfl p
      simp
  simp only [Fintype.prod_boole,hb]

theorem incidence_partition : (incidence G r).denote Fin.elim0 = value G r := by
  classical
  rw [incidence_denote_sum]
  simp only [equality,Fintype.prod_sum,Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [incidence_guard,mul_ite,mul_one,mul_zero]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  unfold value
  apply Fintype.sum_equiv (toInstance G r).complementAssignment
  intro x
  rfl

end
end Paper2.DegreeCSP.Raw
