import Paper2.DegreeCSP.QuarticLiftInstance

/-! Prescribed finite enumeration of the quartic-lift occurrence compiler.
Variable numbers and factor order agree with the deterministic raw layout:
edge ends, then per-vertex hidden variables; per-vertex original factors and
local X copies, then outer X copies. No runtime implementation is asserted. -/
namespace Paper2.DegreeCSP.QuarticLiftInstance
open scoped BigOperators
open Tractable
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (α : Type) : DecidableEq α := Classical.decEq α
local instance (priority := 3000) : DecidableEq Bool := Bool.decEq
variable {V E : Type} [Fintype V] [Fintype E]

abbrev coreScope (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E) {k : ℕ}
    (c : Tag P V E k) (j : Fin (arity P c)) : Hidden P V E :=
  Sum.elim Fin.elim0 id (scope P p c j)

theorem scope_core (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E) {k : ℕ}
    (c : Tag P V E k) (j : Fin (arity P c)) :
    scope P p c j = Sum.inr (coreScope P p c j) := by
  cases c <;> rfl

/-- The caller prescribes every variable ordinal and constraint ordinal. -/
def enumerated (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E) (k : ℕ)
    {N M : ℕ} (he : Hidden P V E ≃ Fin N) (ce : Tag P V E k ≃ Fin M) :
    Instance AlgebraicComplex where
  variableCount := N
  constraints := M
  arity c := arity P (ce.symm c)
  table c := table P (ce.symm c)
  scope c j := he (coreScope P p (ce.symm c) j)

def enumeratedFiber (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E) (k : ℕ)
    {N M : ℕ} (he : Hidden P V E ≃ Fin N) (ce : Tag P V E k ≃ Fin M)
    (w : Hidden P V E) :
    (enumerated P p k he ce).Fiber (he w) ≃
      {o : Σ c : Tag P V E k, Fin (arity P c) // coreScope P p o.1 o.2 = w} := by
  refine Equiv.subtypeEquiv (Equiv.sigmaCongrLeft (β := fun c : Tag P V E k => Fin (arity P c)) ce.symm) ?_
  intro o
  exact he.injective.eq_iff

theorem enumerated_degree (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    (k : ℕ) {N M : ℕ} (he : Hidden P V E ≃ Fin N) (ce : Tag P V E k ≃ Fin M)
    (w : Hidden P V E) :
    (enumerated P p k he ce).degree (he w) =
      (presentation P p k).degree (OrderedPresentation.variableEquiv (Sum.inr w)) := by
  have hc : (enumerated P p k he ce).degree (he w) =
      Nat.card ((enumerated P p k he ce).Fiber (he w)) := by
    exact (@Nat.card_eq_fintype_card ((enumerated P p k he ce).Fiber (he w))
      (@Subtype.fintype (enumerated P p k he ce).Occurrence
        (fun o => (enumerated P p k he ce).route o = he w)
        (fun o => instDecidableEqFin N ((enumerated P p k he ce).route o) (he w))
        inferInstance)).symm
  rw [hc,Nat.card_congr (enumeratedFiber P p k he ce w)]
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_filter,Fintype.sum_sigma]
  rw [presentation_degree]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro j _
  simp only [scope_core,Sum.inr.injEq]

theorem enumerated_divisible (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    {k N M : ℕ} (he : Hidden P V E ≃ Fin N) (ce : Tag P V E k ≃ Fin M)
    (hP : P.DegreeDivisible k) : (enumerated P p k he ce).DegreeDivisible k := by
  have hd := (Presentation.toInstance_divisible (presentation P p k) k).mp (divisible P p hP)
  intro v
  obtain ⟨w,rfl⟩ := he.surjective v
  rw [enumerated_degree]
  exact hd _

theorem enumerated_uses (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    (k : ℕ) {N M : ℕ} (he : Hidden P V E ≃ Fin N) (ce : Tag P V E k ≃ Fin M)
    {F : SignatureFamily AlgebraicComplex} (hP : P.Uses F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F) :
    (enumerated P p k he ce).Uses F := by
  intro c
  change (⟨arity P (ce.symm c),table P (ce.symm c)⟩ : AnySignature AlgebraicComplex) ∈ F
  cases hc : ce.symm c with
  | inl c => exact hP c.2
  | inr c => exact hX

theorem enumerated_partition (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    (k : ℕ) {N M : ℕ} (he : Hidden P V E ≃ Fin N) (ce : Tag P V E k ≃ Fin M) :
    (enumerated P p k he ce).partition = (presentation P p k).value Fin.elim0 := by
  rw [presentation,OrderedPresentation.ordered_value]
  let W (y : Hidden P V E → Bool) : AlgebraicComplex :=
    ∏ c : Tag P V E k, table P c
      (fun j => y (coreScope P p c j))
  let e : (Fin N → Bool) ≃ (Hidden P V E → Bool) :=
    Equiv.arrowCongr he.symm (Equiv.refl Bool)
  calc
    _ = ∑ x : Fin N → Bool, ∏ c : Fin M,
        table P (ce.symm c) (fun j => x (he (coreScope P p (ce.symm c) j))) := by
      unfold Instance.partition Instance.weight enumerated
      refine Finset.sum_congr ?_ ?_
      · ext x
        simp only [Finset.mem_univ]
      intro x _
      rfl
    _ = ∑ x : Fin N → Bool, W (e x) := by
      apply Finset.sum_congr rfl
      intro x _
      exact ce.symm.prod_comp (fun c => table P c
        (fun j => (e x) (coreScope P p c j)))
    _ = ∑ y : Hidden P V E → Bool, W y := by
      exact e.sum_comp W
    _ = _ := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.prod_congr rfl
      intro c _
      congr 1
      funext j
      rw [scope_core]
      rfl

/-- Reordering tags into the exact per-vertex factor layout. -/
def tagOrder (P : Presentation AlgebraicComplex (Fin 2)) (m e k : ℕ) :
    Tag P (Fin m) (Fin e) k ≃
      (Fin m × (Fin P.constraints ⊕ (Fin 2 × Fin k))) ⊕ (Fin e × Fin k) where
  toFun
    | Sum.inl (v,c) => Sum.inl (v,Sum.inl c)
    | Sum.inr (Sum.inl (v,j),q) => Sum.inl (v,Sum.inr (j,q))
    | Sum.inr (Sum.inr r,q) => Sum.inr (r,q)
  invFun
    | Sum.inl (v,Sum.inl c) => Sum.inl (v,c)
    | Sum.inl (v,Sum.inr (j,q)) => Sum.inr (Sum.inl (v,j),q)
    | Sum.inr (r,q) => Sum.inr (Sum.inr r,q)
  left_inv := by rintro (⟨v,c⟩ | ⟨(⟨v,j⟩ | r),q⟩) <;> rfl
  right_inv := by rintro (⟨v,(c | ⟨j,q⟩)⟩ | ⟨r,q⟩) <;> rfl

def variableIndex (P : Presentation AlgebraicComplex (Fin 2)) (m e : ℕ) :
    Hidden P (Fin m) (Fin e) ≃ Fin (2 * e + m * P.hiddenCount) :=
  ((Equiv.sumCongr
    ((Equiv.prodCongr (Equiv.refl (Fin e)) finTwoEquiv.symm).trans finProdFinEquiv)
    finProdFinEquiv).trans finSumFinEquiv).trans
      (finCongr (congrArg (fun a => a + m * P.hiddenCount) (Nat.mul_comm e 2)))

def constraintIndex (P : Presentation AlgebraicComplex (Fin 2)) (m e k : ℕ) :
    Tag P (Fin m) (Fin e) k ≃ Fin (m * (P.constraints + 2 * k) + e * k) :=
  (tagOrder P m e k).trans
    ((Equiv.sumCongr
      ((Equiv.prodCongr (Equiv.refl (Fin m))
        ((Equiv.sumCongr (Equiv.refl (Fin P.constraints)) finProdFinEquiv).trans
          finSumFinEquiv)).trans finProdFinEquiv)
      finProdFinEquiv).trans finSumFinEquiv)

/-- Exactly the variable count and constraint count of the literal emitter. -/
abbrev ordered (P : Presentation AlgebraicComplex (Fin 2))
    {m e : ℕ} (p : Ports (Fin m) (Fin e)) (k : ℕ) : Instance AlgebraicComplex :=
  enumerated P p k (variableIndex P m e) (constraintIndex P m e k)

theorem ordered_partition (P : Presentation AlgebraicComplex (Fin 2))
    {m e : ℕ} (p : Ports (Fin m) (Fin e)) {g : Signature AlgebraicComplex 2}
    (hP : P.value = g) {k : ℕ} (hk : 0 < k) :
    (ordered P p k).partition = (network p g).denote Fin.elim0 := by
  rw [ordered,enumerated_partition]
  exact value P p hP hk

theorem ordered_divisible (P : Presentation AlgebraicComplex (Fin 2))
    {m e : ℕ} (p : Ports (Fin m) (Fin e)) {k : ℕ} (hP : P.DegreeDivisible k) :
    (ordered P p k).DegreeDivisible k :=
  enumerated_divisible P p (variableIndex P m e) (constraintIndex P m e k) hP

theorem ordered_uses (P : Presentation AlgebraicComplex (Fin 2))
    {m e : ℕ} (p : Ports (Fin m) (Fin e)) (k : ℕ)
    {F : SignatureFamily AlgebraicComplex} (hP : P.Uses F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F) :
    (ordered P p k).Uses F :=
  enumerated_uses P p k (variableIndex P m e) (constraintIndex P m e k) hP hX

@[simp] theorem variableIndex_endpoint_val (P : Presentation AlgebraicComplex (Fin 2))
    (m e : ℕ) (r : Fin e) (b : Bool) :
    (variableIndex P m e (Sum.inl (r,b))).val = 2 * r.val + if b then 1 else 0 := by
  cases b <;> simp [variableIndex,finProdFinEquiv,finTwoEquiv] <;> omega
@[simp] theorem variableIndex_hidden_val (P : Presentation AlgebraicComplex (Fin 2))
    (m e : ℕ) (v : Fin m) (h : Fin P.hiddenCount) :
    (variableIndex P m e (Sum.inr (v,h))).val = 2 * e + v.val * P.hiddenCount + h.val := by
  simp [variableIndex,finProdFinEquiv]
  ring
@[simp] theorem constraintIndex_old_val (P : Presentation AlgebraicComplex (Fin 2))
    (m e k : ℕ) (v : Fin m) (c : Fin P.constraints) :
    (constraintIndex P m e k (Sum.inl (v,c))).val = v.val * (P.constraints + 2*k) + c.val := by
  simp [constraintIndex,tagOrder,finProdFinEquiv]
  ring
@[simp] theorem constraintIndex_local_val (P : Presentation AlgebraicComplex (Fin 2))
    (m e k : ℕ) (v : Fin m) (j : Fin 2) (q : Fin k) :
    (constraintIndex P m e k (Sum.inr (Sum.inl (v,j),q))).val =
      v.val * (P.constraints + 2*k) + P.constraints + j.val*k + q.val := by
  simp [constraintIndex,tagOrder,finProdFinEquiv]
  ring
@[simp] theorem constraintIndex_outer_val (P : Presentation AlgebraicComplex (Fin 2))
    (m e k : ℕ) (r : Fin e) (q : Fin k) :
    (constraintIndex P m e k (Sum.inr (Sum.inr r,q))).val =
      m * (P.constraints + 2*k) + r.val*k + q.val := by
  simp [constraintIndex,tagOrder,finProdFinEquiv]
  ring

end
end Paper2.DegreeCSP.QuarticLiftInstance
