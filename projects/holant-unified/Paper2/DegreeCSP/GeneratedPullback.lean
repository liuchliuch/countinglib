import Paper2.DegreeCSP.GeneratedCompose

/-! Arbitrary boundary identification of actual generated presentations.
Every ordered constraint remains present. Boundary degrees add over the map's
fibers; no occurrence is assigned to an unused new boundary variable. -/
namespace Paper2.DegreeCSP
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
attribute [local instance] Classical.propDecidable

namespace Presentation
variable {K B C : Type}

def pullBoundary (P : Presentation K B) (r : B → C) : Presentation K C where
  hiddenCount := P.hiddenCount
  constraints := P.constraints
  arity := P.arity
  constraint := P.constraint
  scope c j := Sum.map r id (P.scope c j)

private theorem occurrence_boundary_count [Fintype B] [DecidableEq B] [DecidableEq C] (r : B → C)
    {H : Type} [DecidableEq H] (p : B ⊕ H) (c : C) :
    (if Sum.map r id p=Sum.inl c then 1 else 0) =
      ∑ b : B,if r b=c then (if p=Sum.inl b then 1 else 0) else (0 : ℕ) := by
  classical
  cases p with
  | inl b0 =>
    simp only [Sum.map_inl,Sum.inl.injEq]
    have he (b : B) : (if r b=c then (if b0=b then 1 else 0) else (0 : ℕ)) =
        if b0=b then (if r b=c then 1 else 0) else 0 := by
      by_cases h : b0=b <;> simp [h]
    simp_rw [he]
    simp
  | inr h => simp

theorem pull_boundary_degree [Fintype B] (P : Presentation K B) (r : B → C) (c : C) :
    (P.pullBoundary r).degree (Sum.inl c) =
      ∑ b : B,if r b=c then P.degree (Sum.inl b) else 0 := by
  classical
  rw [degree_eq_sum]
  change (∑ d : Fin P.constraints, ∑ j : Fin (P.arity d),
    if Sum.map r id (P.scope d j)=Sum.inl c then 1 else 0) = _
  calc
    _ = ∑ d, ∑ j : Fin (P.arity d), ∑ b : B,
        if r b=c then (if P.scope d j=Sum.inl b then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      apply Finset.sum_congr rfl
      intro j _
      exact occurrence_boundary_count r (P.scope d j) c
    _ = ∑ d, ∑ b : B, ∑ j : Fin (P.arity d),
        if r b=c then (if P.scope d j=Sum.inl b then 1 else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro d _
      exact Finset.sum_comm
    _ = ∑ b : B, ∑ d, ∑ j : Fin (P.arity d),
        if r b=c then (if P.scope d j=Sum.inl b then 1 else 0) else 0 := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases h : r b=c <;> simp [h,degree_eq_sum]

private theorem map_hidden_iff (r : B → C) {H : Type} (p : B ⊕ H) (h : H) :
    (Sum.map r id p=Sum.inr h) ↔ p=Sum.inr h := by cases p <;> simp

theorem pull_hidden_degree (P : Presentation K B) (r : B → C) (h : Fin P.hiddenCount) :
    (P.pullBoundary r).degree (Sum.inr h) = P.degree (Sum.inr h) := by
  simp only [degree_eq_sum,pullBoundary,map_hidden_iff]

theorem pull_divisible [Fintype B] (P : Presentation K B) (r : B → C) {k : ℕ}
    (hP : P.DegreeDivisible k) : (P.pullBoundary r).DegreeDivisible k := by
  intro v
  cases v with
  | inl c =>
    rw [pull_boundary_degree]
    apply Finset.dvd_sum
    intro b _
    by_cases h : r b=c
    · simpa only [h,ite_true] using hP (Sum.inl b)
    · simp [h]
  | inr h =>
    rw [pull_hidden_degree]
    exact hP (Sum.inr h)

theorem pull_uses (P : Presentation K B) (r : B → C) {F : SignatureFamily K}
    (hP : P.Uses F) : (P.pullBoundary r).Uses F := hP

theorem pull_value [CommSemiring K] (P : Presentation K B) (r : B → C) (x : C → Bool) :
    (P.pullBoundary r).value x = P.value (fun b=>x (r b)) := by
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.prod_congr rfl
  intro c _
  congr 1
  funext j
  change Sum.elim x y (Sum.map r id (P.scope c j)) = Sum.elim (fun b=>x (r b)) y (P.scope c j)
  cases P.scope c j <;> rfl

end Presentation

/-- Identifications, duplications, and unused output coordinates all preserve
degree-generated membership, with the original literal constraints. -/
theorem generated_pullback {K : Type} [CommSemiring K] {F : SignatureFamily K}
    {k n m : ℕ} {f : Signature K n} (hf : Generated F k f) (r : Fin n → Fin m) :
    Generated F k (fun x=>f (fun i=>x (r i))) := by
  obtain ⟨P,hPF,hPk,hPf⟩ := hf
  refine ⟨P.pullBoundary r,P.pull_uses r hPF,P.pull_divisible r hPk,?_⟩
  funext x
  rw [Presentation.pull_value,hPf]

end
end Paper2.DegreeCSP
