import Paper2.DegreeCSP.Model
import Paper2.DegreeCSP.BooleanSupport

/-! Literal degree-generated partial tables. A presentation counts every ordered
scope position, including repeated variables, and sums its actual hidden Boolean
variables. Degree divisibility applies to boundary and hidden variables alike. -/
namespace Paper2.DegreeCSP
open scoped BigOperators
noncomputable section

structure Presentation (K B : Type) where
  hiddenCount : ℕ
  constraints : ℕ
  arity : Fin constraints → ℕ
  constraint : (c : Fin constraints) → Signature K (arity c)
  scope : (c : Fin constraints) → Fin (arity c) → B ⊕ Fin hiddenCount

namespace Presentation
variable {K B : Type} (P : Presentation K B)

abbrev Occurrence := Σ c : Fin P.constraints, Fin (P.arity c)
def route (p : P.Occurrence) : B ⊕ Fin P.hiddenCount := P.scope p.1 p.2
abbrev Fiber (v : B ⊕ Fin P.hiddenCount) := {p : P.Occurrence // P.route p = v}
def degree (v : B ⊕ Fin P.hiddenCount) : ℕ := Nat.card (P.Fiber v)
def DegreeDivisible (k : ℕ) : Prop := ∀ v, k ∣ P.degree v
def Uses (F : SignatureFamily K) : Prop :=
  ∀ c, (⟨P.arity c,P.constraint c⟩ : AnySignature K) ∈ F
def value [CommSemiring K] (x : B → Bool) : K :=
  ∑ y : Fin P.hiddenCount → Bool,
    ∏ c, P.constraint c (fun i => Sum.elim x y (P.scope c i))

/-- The closed incidence model is obtained by the literal ordered boundary-
hidden variable equivalence, without changing constraints or occurrences. -/
def toInstance {n : ℕ} (P : Presentation K (Fin n)) : Instance K where
  variableCount := n + P.hiddenCount
  constraints := P.constraints
  arity := P.arity
  table := P.constraint
  scope c i := finSumFinEquiv (P.scope c i)

theorem toInstance_uses {n : ℕ} (P : Presentation K (Fin n))
    (F : SignatureFamily K) : P.toInstance.Uses F ↔ P.Uses F := Iff.rfl

def toInstanceFiber {n : ℕ} (P : Presentation K (Fin n))
    (v : Fin n ⊕ Fin P.hiddenCount) :
    P.toInstance.Fiber (finSumFinEquiv v) ≃ P.Fiber v where
  toFun p := ⟨p.val,finSumFinEquiv.injective p.property⟩
  invFun p := ⟨p.val,congrArg finSumFinEquiv p.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem toInstance_degree {n : ℕ} (P : Presentation K (Fin n))
    (v : Fin n ⊕ Fin P.hiddenCount) :
    P.toInstance.degree (finSumFinEquiv v) = P.degree v :=
  by
    have h := Nat.card_congr
      ((P.toInstance.fiberPorts (finSumFinEquiv v)).trans (P.toInstanceFiber v))
    simpa only [Nat.card_fin,degree] using h

theorem toInstance_divisible {n : ℕ} (P : Presentation K (Fin n)) (k : ℕ) :
    P.toInstance.DegreeDivisible k ↔ P.DegreeDivisible k := by
  constructor
  · intro h v
    simpa only [toInstance_degree] using h (finSumFinEquiv v)
  · intro h v
    obtain ⟨w,rfl⟩ := finSumFinEquiv.surjective v
    simpa only [toInstance_degree] using h w

/-- Summing the actual partial table over all boundary assignments is exactly
the closed model's partition, also for empty boundary or hidden sets. -/
theorem toInstance_partition {n : ℕ} [CommSemiring K]
    (P : Presentation K (Fin n)) :
    P.toInstance.partition = ∑ x : Fin n → Bool, P.value x := by
  classical
  let e : (Fin (n + P.hiddenCount) → Bool) ≃
      (Fin n → Bool) × (Fin P.hiddenCount → Bool) :=
    (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
      (Equiv.sumArrowEquivProdArrow (Fin n) (Fin P.hiddenCount) Bool)
  let w : (Fin (n + P.hiddenCount) → Bool) → K := fun z =>
    ∏ c, P.constraint c (fun i => z (finSumFinEquiv (P.scope c i)))
  change (∑ z, w z) = _
  calc
    _ = ∑ p, w (e.symm p) := (e.symm.sum_comp w).symm
    _ = ∑ x : Fin n → Bool, P.value x := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.prod_congr rfl
      intro c _
      congr 1
      funext i
      simp [e,Equiv.arrowCongr,Equiv.sumArrowEquivProdArrow]

/-- q copies of one table have each boundary occurrence degree exactly q. -/
def power {n : ℕ} (f : Signature K n) (q : ℕ) : Presentation K (Fin n) where
  hiddenCount := 0
  constraints := q
  arity := fun _ => n
  constraint := fun _ => f
  scope := fun _ i => Sum.inl i

def powerFiber {n : ℕ} (f : Signature K n) (q : ℕ) (j : Fin n) :
    (power f q).Fiber (Sum.inl j) ≃ Fin q where
  toFun p := p.val.1
  invFun c := ⟨⟨c,j⟩,rfl⟩
  left_inv p := by
    apply Subtype.ext
    have h : p.val.2 = j := Sum.inl.inj p.property
    exact Sigma.ext rfl (heq_of_eq h.symm)
  right_inv _ := rfl

theorem power_degree {n : ℕ} (f : Signature K n) (q : ℕ) (j : Fin n) :
    (power f q).degree (Sum.inl j) = q := by
  exact (Nat.card_congr (powerFiber f q j)).trans (Nat.card_fin q)

theorem power_divisible {n : ℕ} (f : Signature K n) {q k : ℕ} (h : k ∣ q) :
    (power f q).DegreeDivisible k := by
  intro v
  cases v with
  | inl j => simpa only [power_degree] using h
  | inr j => exact Fin.elim0 j

theorem power_uses {n : ℕ} (F : SignatureFamily K) (f : Signature K n)
    (hf : (⟨n,f⟩ : AnySignature K) ∈ F) (q : ℕ) : (power f q).Uses F :=
  fun _ => hf

theorem power_value {n : ℕ} [CommSemiring K] (f : Signature K n) (q : ℕ)
    (x : Fin n → Bool) : (power f q).value x = f x ^ q := by
  change (∑ _ : Fin 0 → Bool, ∏ _ : Fin q, f x) = _
  have hcq : (Finset.univ : Finset (Fin q)).card = q := Fintype.card_fin q
  have hc0 : (Finset.univ : Finset (Fin 0 → Bool)).card = 1 :=
    Fintype.card_unique
  simp only [Finset.prod_const,Finset.sum_const,hcq,hc0,one_nsmul]


end Presentation

/-- Membership is witnessed by a finite ordered partial CSP presentation. -/
def Generated {K : Type} [CommSemiring K] (F : SignatureFamily K) (k : ℕ)
    {n : ℕ} (f : Signature K n) : Prop :=
  ∃ P : Presentation K (Fin n), P.Uses F ∧ P.DegreeDivisible k ∧ P.value = f

theorem generated_power {K : Type} [CommSemiring K] (F : SignatureFamily K)
    {n : ℕ} (f : Signature K n) (hf : (⟨n,f⟩ : AnySignature K) ∈ F)
    {q k : ℕ} (hq : k ∣ q) : Generated F k (fun x => f x ^ q) := by
  refine ⟨Presentation.power f q,Presentation.power_uses F f hf q,
    Presentation.power_divisible f hq,?_⟩
  funext x
  exact Presentation.power_value f q x

end
end Paper2.DegreeCSP
