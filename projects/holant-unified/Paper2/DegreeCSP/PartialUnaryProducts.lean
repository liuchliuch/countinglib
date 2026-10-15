import Paper2.DegreeCSP.GeneratedCompose
import Paper2.Tractable.Affine
import Paper2.DegreeCSP.CyclicPhaseCharacterGenerators

/-! Products of partial unary contexts are actual finite presentations.
Their hidden variables remain disjoint, their boundary degrees add, and their
values multiply. Divisibility is required only of the final boundary degree.
-/
namespace Paper2.DegreeCSP.PartialUnaryProducts
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {K : Type} [CommSemiring K] {n : ℕ}

def HiddenDivisible (P : Presentation K (Fin n)) (k : ℕ) : Prop :=
  ∀ h : Fin P.hiddenCount, k ∣ P.degree (Sum.inr h)

omit [CommSemiring K] in
/-- A disjoint product does not add incidences to either hidden block. -/
theorem product_hidden_divisible (P Q : Presentation K (Fin n)) {k : ℕ}
    (hP : HiddenDivisible P k) (hQ : HiddenDivisible Q k) :
    HiddenDivisible (P.disjointProduct Q) k := by
  intro h
  obtain ⟨w,hw⟩ := (Fintype.equivFin (Fin P.hiddenCount ⊕ Fin Q.hiddenCount)).surjective h
  subst h
  rcases w with p | q
  · simpa only [OrderedPresentation.variableEquiv,Equiv.sumCongr_apply,
      Equiv.refl_apply,Sum.map_inr] using
      (P.product_hidden_left_degree Q p).symm ▸ hP p
  · simpa only [OrderedPresentation.variableEquiv,Equiv.sumCongr_apply,
      Equiv.refl_apply,Sum.map_inr] using
      (P.product_hidden_right_degree Q q).symm ▸ hQ q

/-- The empty product has no clauses or hidden variables. -/
def empty : Presentation K (Fin n) :=
  Presentation.power (fun _ : Fin n → Bool => (1 : K)) 0

theorem empty_uses (F : SignatureFamily K) : (empty (K:=K) (n:=n)).Uses F :=
  fun c => Fin.elim0 c

theorem empty_boundary_degree (i : Fin n) :
    (empty (K:=K) (n:=n)).degree (Sum.inl i) = 0 :=
  Presentation.power_degree _ _ _

theorem empty_hidden_divisible (k : ℕ) : HiddenDivisible (empty (K:=K) (n:=n)) k :=
  fun h => Fin.elim0 h

theorem empty_value (x : Fin n → Bool) : (empty (K:=K) (n:=n)).value x = 1 := by
  rw [empty,Presentation.power_value,pow_zero]

/-- Each occurrence uses its own copy of every hidden variable. -/
def repeated (P : Presentation K (Fin n)) : ℕ → Presentation K (Fin n)
  | 0 => empty
  | q+1 => (repeated P q).disjointProduct P

theorem repeated_uses (P : Presentation K (Fin n)) {F : SignatureFamily K}
    (hP : P.Uses F) (q : ℕ) : (repeated P q).Uses F := by
  induction q with
  | zero => exact empty_uses F
  | succ q ih => exact Presentation.product_uses _ _ ih hP

theorem repeated_boundary_degree (P : Presentation K (Fin n)) (q : ℕ) (i : Fin n) :
    (repeated P q).degree (Sum.inl i) = q * P.degree (Sum.inl i) := by
  induction q with
  | zero => simp only [repeated,empty_boundary_degree,zero_mul]
  | succ q ih =>
    rw [repeated,Presentation.product_boundary_degree,ih,Nat.succ_mul]

theorem repeated_hidden_divisible (P : Presentation K (Fin n)) {k : ℕ}
    (hP : HiddenDivisible P k) (q : ℕ) : HiddenDivisible (repeated P q) k := by
  induction q with
  | zero => exact empty_hidden_divisible k
  | succ q ih => exact product_hidden_divisible _ _ ih hP

theorem repeated_value (P : Presentation K (Fin n)) (q : ℕ) (x : Fin n → Bool) :
    (repeated P q).value x = P.value x ^ q := by
  induction q with
  | zero => simp only [repeated,empty_value,pow_zero]
  | succ q ih => rw [repeated,Presentation.product_value,ih,pow_succ]

/-- A finite multiset of contexts sharing only their boundary variables. -/
def product : (s : ℕ) → (Fin s → Presentation K (Fin n)) →
    (Fin s → ℕ) → Presentation K (Fin n)
  | 0,_,_ => empty
  | s+1,P,q => (repeated (P 0) (q 0)).disjointProduct
      (product s (fun i => P i.succ) (fun i => q i.succ))

theorem product_uses (s : ℕ) (P : Fin s → Presentation K (Fin n)) (q : Fin s → ℕ)
    {F : SignatureFamily K} (uses : ∀ i, (P i).Uses F) :
    (product s P q).Uses F := by
  induction s with
  | zero => exact empty_uses F
  | succ s ih =>
    exact Presentation.product_uses _ _ (repeated_uses _ (uses 0) _)
      (ih (fun i => P i.succ) (fun i => q i.succ) (fun i => uses i.succ))

theorem product_boundary_degree (s : ℕ) (P : Fin s → Presentation K (Fin n))
    (q : Fin s → ℕ) (i : Fin n) :
    (product s P q).degree (Sum.inl i) = ∑ j, q j * (P j).degree (Sum.inl i) := by
  induction s with
  | zero => simp only [product,empty_boundary_degree,Finset.univ_eq_empty,Finset.sum_empty]
  | succ s ih =>
    rw [product,Presentation.product_boundary_degree,repeated_boundary_degree,
      ih,Fin.sum_univ_succ]

theorem product_hidden_divisible_family (s : ℕ) (P : Fin s → Presentation K (Fin n))
    (q : Fin s → ℕ) {k : ℕ} (hidden : ∀ i, HiddenDivisible (P i) k) :
    HiddenDivisible (product s P q) k := by
  induction s with
  | zero => exact empty_hidden_divisible k
  | succ s ih =>
    exact product_hidden_divisible _ _ (repeated_hidden_divisible _ (hidden 0) _)
      (ih (fun i => P i.succ) (fun i => q i.succ) (fun i => hidden i.succ))

theorem product_value (s : ℕ) (P : Fin s → Presentation K (Fin n)) (q : Fin s → ℕ)
    (x : Fin n → Bool) : (product s P q).value x = ∏ i, (P i).value x ^ q i := by
  induction s with
  | zero => simp only [product,empty_value,Finset.univ_eq_empty,Finset.prod_empty]
  | succ s ih =>
    rw [product,Presentation.product_value,repeated_value,ih,Fin.prod_univ_succ]

/-- Only the accumulated boundary degree needs to be a multiple of k. -/
theorem generated {F : SignatureFamily K} {k s : ℕ}
    (P : Fin s → Presentation K (Fin 1)) (q : Fin s → ℕ)
    (uses : ∀ i, (P i).Uses F) (hidden : ∀ i, HiddenDivisible (P i) k)
    (boundary : k ∣ ∑ i, q i * (P i).degree (Sum.inl 0)) :
    Generated F k (fun z => ∏ i, (P i).value z ^ q i) := by
  refine ⟨product s P q,product_uses s P q uses,?_,?_⟩
  · rintro (i | h)
    · rw [Fin.eq_zero i,product_boundary_degree]
      exact boundary
    · exact product_hidden_divisible_family s P q hidden h
  · funext x
    exact product_value s P q x

theorem generated_of_degrees {F : SignatureFamily K} {k s : ℕ}
    (P : Fin s → Presentation K (Fin 1)) (q d : Fin s → ℕ)
    (uses : ∀ i, (P i).Uses F) (hidden : ∀ i, HiddenDivisible (P i) k)
    (degree : ∀ i, (P i).degree (Sum.inl 0) = d i)
    (boundary : k ∣ ∑ i, q i * d i) :
    Generated F k (fun z => ∏ i, (P i).value z ^ q i) := by
  apply generated P q uses hidden
  simpa only [degree] using boundary

/-- Affineness of the actually generated product imposes the finite cycle
condition on the original context ratios, including zero multiplicities. -/
theorem ratio_four {F : SignatureFamily AlgebraicComplex} {k s : ℕ}
    (affine : ∀ g : Signature AlgebraicComplex 1, Generated F k g → Affine g)
    (P : Fin s → Presentation AlgebraicComplex (Fin 1)) (q : Fin s → ℕ)
    (uses : ∀ i, (P i).Uses F) (hidden : ∀ i, HiddenDivisible (P i) k)
    (boundary : k ∣ ∑ i, q i * (P i).degree (Sum.inl 0))
    (h0 : ∀ i, (P i).value ![false] ≠ 0)
    (h1 : ∀ i, (P i).value ![true] ≠ 0) :
    (∏ i, ((P i).value ![true] / (P i).value ![false]) ^ q i) ^ 4 = 1 := by
  classical
  let g : Signature AlgebraicComplex 1 := fun z => ∏ i, (P i).value z ^ q i
  have hg : Generated F k g := generated P q uses hidden boundary
  have hg0 : g ![false] ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (h0 i))
  have hg1 : g ![true] ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (h1 i))
  have he := (affine g hg).fourth_power_eq ![true] ![false] hg1 hg0
  have hr : (g ![true] / g ![false]) ^ 4 = 1 := by
    rw [div_pow,he,div_self (pow_ne_zero _ hg0)]
  simpa only [g,Finset.prod_div_distrib,div_pow] using hr

/-- The cycle constraints of the actual products determine one common
character phase for every partial context's occupied boundary degree. -/
theorem common_phase {F : SignatureFamily AlgebraicComplex} {k s : ℕ}
    (hk : 0 < k)
    (affine : ∀ g : Signature AlgebraicComplex 1, Generated F k g → Affine g)
    (P : Fin s → Presentation AlgebraicComplex (Fin 1))
    (uses : ∀ i, (P i).Uses F) (hidden : ∀ i, HiddenDivisible (P i) k)
    (h0 : ∀ i, (P i).value ![false] ≠ 0)
    (h1 : ∀ i, (P i).value ![true] ≠ 0) :
    ∃ theta : AlgebraicComplex, theta^k = 1 ∧ ∀ i,
      ((P i).value ![true] / (P i).value ![false]) ^ 4 =
        theta ^ (P i).degree (Sum.inl 0) := by
  apply CyclicPhaseCharacterGenerators.exists_phase_of_cycles hk
    (fun i => (P i).degree (Sum.inl 0))
    (fun i => ((P i).value ![true] / (P i).value ![false]) ^ 4)
  intro q boundary
  have h := ratio_four affine P q uses hidden boundary h0 h1
  rw [← Finset.prod_pow] at h
  convert h using 1
  apply Finset.prod_congr rfl
  intro i _
  rw [←pow_mul,←pow_mul,Nat.mul_comm]

theorem common_phase_of_degrees {F : SignatureFamily AlgebraicComplex} {k s : ℕ}
    (hk : 0 < k)
    (affine : ∀ g : Signature AlgebraicComplex 1, Generated F k g → Affine g)
    (P : Fin s → Presentation AlgebraicComplex (Fin 1)) (d : Fin s → ℕ)
    (uses : ∀ i, (P i).Uses F) (hidden : ∀ i, HiddenDivisible (P i) k)
    (degree : ∀ i, (P i).degree (Sum.inl 0) = d i)
    (h0 : ∀ i, (P i).value ![false] ≠ 0)
    (h1 : ∀ i, (P i).value ![true] ≠ 0) :
    ∃ theta : AlgebraicComplex, theta^k = 1 ∧ ∀ i,
      ((P i).value ![true] / (P i).value ![false]) ^ 4 = theta ^ d i := by
  simpa only [degree] using common_phase hk affine P uses hidden h0 h1

end
end Paper2.DegreeCSP.PartialUnaryProducts

