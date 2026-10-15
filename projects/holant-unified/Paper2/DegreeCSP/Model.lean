import Paper2.NetworkSubstitution

/-! A finite Boolean CSP retains every ordered constraint position, even when
several positions refer to the same variable. Degree means the number of those
positions. The sum defining equality also handles degree zero: the two Boolean
assignments of an unused variable contribute the literal nullary value two. -/
namespace Paper2.DegreeCSP
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure Instance (K : Type) where
  variableCount : ℕ
  constraints : ℕ
  arity : Fin constraints → ℕ
  table : (c : Fin constraints) → Signature K (arity c)
  scope : (c : Fin constraints) → Fin (arity c) → Fin variableCount

namespace Instance
variable {K : Type} (I : Instance K)

abbrev Occurrence := Σ c : Fin I.constraints, Fin (I.arity c)

def route (p : I.Occurrence) : Fin I.variableCount := I.scope p.1 p.2

abbrev Fiber (v : Fin I.variableCount) := {p : I.Occurrence // I.route p = v}

def degree (v : Fin I.variableCount) : ℕ := by
  classical
  exact Fintype.card (I.Fiber v)

def DegreeDivisible (k : ℕ) : Prop := ∀ v, k ∣ I.degree v

def Uses (F : SignatureFamily K) : Prop :=
  ∀ c, (⟨I.arity c,I.table c⟩ : AnySignature K) ∈ F

def weight [CommSemiring K] (z : I.Occurrence → Bool) : K :=
  ∏ c, I.table c (fun j => z ⟨c,j⟩)

def partition [CommSemiring K] : K :=
  ∑ x : Fin I.variableCount → Bool, I.weight (fun p => x (I.route p))

/-- The actual degree enumeration gives one port to each separate occurrence. -/
def fiberPorts (v : Fin I.variableCount) : Fin (I.degree v) ≃ I.Fiber v := by
  classical
  exact (Fintype.equivFin (I.Fiber v)).symm

def variablePorts : (Σ v : Fin I.variableCount, Fin (I.degree v)) ≃ I.Occurrence :=
  (Equiv.sigmaCongrRight I.fiberPorts).trans (Equiv.sigmaFiberEquiv I.route)

@[simp] theorem variablePorts_apply (v : Fin I.variableCount) (j : Fin (I.degree v)) :
    I.variablePorts ⟨v,j⟩ = (I.fiberPorts v j).val := rfl

@[simp] theorem variablePorts_route (v : Fin I.variableCount) (j : Fin (I.degree v)) :
    I.route (I.variablePorts ⟨v,j⟩) = v := (I.fiberPorts v j).property

end Instance

def equality {K : Type} [CommSemiring K] (n : ℕ) : Signature K n := by
  classical
  exact fun x => ∑ b : Bool, ∏ i : Fin n, if x i = b then 1 else 0

theorem equality_eq {K : Type} [CommSemiring K] (n : ℕ) (x : Fin n → Bool) :
    equality (K := K) n x =
      (if x = (fun _ => false) then 1 else 0) +
      (if x = (fun _ => true) then 1 else 0) := by
  classical
  simp only [equality,Fintype.sum_bool,Fintype.prod_boole,funext_iff]
  by_cases h0 : ∀ i, x i = false <;> by_cases h1 : ∀ i, x i = true
  · simp only [if_pos h0,if_pos h1]
  · simp only [if_pos h0,if_neg h1,zero_add,add_zero]
  · simp only [if_neg h0,if_pos h1,zero_add,add_zero]
  · simp only [if_neg h0,if_neg h1]

@[simp] theorem equality_zero {K : Type} [CommSemiring K] (x : Fin 0 → Bool) :
    equality (K := K) 0 x = 2 := by
  simp [equality]

end
end Paper2.DegreeCSP
