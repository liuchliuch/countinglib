import Paper2.DegreeCSP.TwoRowRestriction
import Holant.Proofs.Hardness.EOBinaryPlaneCore

/-! Pure finite occurrence compiler for a closed native-X graph of the
literal quaternary binary lift. Each port occurrence remains a separate
variable, every auxiliary X is repeated k times, and all vertex-presentation
hidden variables remain independently summed. -/
namespace Paper2.DegreeCSP.QuarticLiftInstance
open scoped BigOperators
open Tractable
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (α : Type) : DecidableEq α := Classical.decEq α
local instance (priority := 3000) : DecidableEq Bool := Bool.decEq

variable {V E : Type} [Fintype V] [Fintype E]

/-- Literal graph shape: each ordered quaternary port is exactly one end of
one edge, with no omitted or identified occurrence. -/
abbrev Ports (V E : Type) := (V × Fin 4) ≃ (E × Bool)

def closedEnds (α : Type) : α ≃ (Fin 0 ⊕ α) where
  toFun := Sum.inr
  invFun := Sum.elim Fin.elim0 id
  left_inv _ := rfl
  right_inv := by rintro (i | x); exact Fin.elim0 i; rfl

def network (p : Ports V E) (g : Signature AlgebraicComplex 2) :
    FiniteNetwork AlgebraicComplex V E 0 where
  arity := fun _ => 4
  ports := (Equiv.sigmaEquivProd V (Fin 4)).trans
    (p.trans (closedEnds (E × Bool)))
  vertex := fun _ => Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore.lift g
  edge := fun _ => Signature.disequality

/-- The retained conditional lift equals the literal binary table and its
local opposite-pair indicators, with exactly unit coefficients. -/
theorem lift_product (g : Signature AlgebraicComplex 2) (x : Fin 4 → Bool) :
    Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore.lift g x = g ![x 0,x 2] * Signature.disequality (x 0) (x 1) *
      Signature.disequality (x 2) (x 3) := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore.lift,Signature.disequality,h0,h1,h2,h3]

abbrev mainPort (i : Fin 2) : Fin 4 := ⟨2 * i.val, by have := i.isLt; omega⟩
abbrev pairPort (i j : Fin 2) : Fin 4 := (![![0,1],![2,3]] i) j
abbrev endBit (j : Fin 2) : Bool := ![false,true] j

abbrev Hidden (P : Presentation AlgebraicComplex (Fin 2)) (V E : Type) :=
  (E × Bool) ⊕ (V × Fin P.hiddenCount)
abbrev Added (V E : Type) := (V × Fin 2) ⊕ E
abbrev Tag (P : Presentation AlgebraicComplex (Fin 2)) (V E : Type) (k : ℕ) :=
  (V × Fin P.constraints) ⊕ (Added V E × Fin k)

abbrev embed (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E) (v : V) :
    Fin 2 ⊕ Fin P.hiddenCount → Hidden P V E
  | Sum.inl i => Sum.inl (p (v,mainPort i))
  | Sum.inr h => Sum.inr (v,h)

theorem embed_injective (P : Presentation AlgebraicComplex (Fin 2))
    (p : Ports V E) (v : V) : Function.Injective (embed P p v) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      have hh : mainPort a = mainPort b := (congrArg Prod.snd
        (p.injective (Sum.inl.inj hab)))
      have hv : 2 * a.val = 2 * b.val := congrArg Fin.val hh
      exact congrArg Sum.inl (Fin.ext (by omega))
    | inr b => simp only [embed,Sum.inl_ne_inr] at hab
  | inr a =>
    cases b with
    | inl b => simp only [embed,Sum.inr_ne_inl] at hab
    | inr b => exact congrArg Sum.inr (congrArg Prod.snd (Sum.inr.inj hab))

abbrev arity (P : Presentation AlgebraicComplex (Fin 2)) {k : ℕ} : Tag P V E k → ℕ
  | Sum.inl c => P.arity c.2
  | Sum.inr _ => 2
abbrev table (P : Presentation AlgebraicComplex (Fin 2)) {k : ℕ} :
    (c : Tag P V E k) → Signature AlgebraicComplex (arity P c)
  | Sum.inl c => P.constraint c.2
  | Sum.inr _ => kernelSignature Signature.disequality
abbrev addedScope (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E) :
    Added V E → Fin 2 → Hidden P V E
  | Sum.inl c, j => Sum.inl (p (c.1,pairPort c.2 j))
  | Sum.inr e, j => Sum.inl (e,endBit j)
abbrev scope (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E) {k : ℕ} :
    (c : Tag P V E k) → Fin (arity P c) → Fin 0 ⊕ Hidden P V E
  | Sum.inl c, j => Sum.inr (embed P p c.1 (P.scope c.2 j))
  | Sum.inr c, j => Sum.inr (addedScope P p c.1 j)

abbrev presentation (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    (k : ℕ) : Presentation AlgebraicComplex (Fin 0) :=
  OrderedPresentation.ordered (arity P (k := k)) (table P) (scope P p)
abbrev compile (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    (k : ℕ) : Instance AlgebraicComplex := (presentation P p k).toInstance

theorem uses (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E) (k : ℕ)
    {F : SignatureFamily AlgebraicComplex} (hP : P.Uses F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F) :
    (compile P p k).Uses F := by
  apply (Presentation.toInstance_uses (presentation P p k) F).mpr
  apply OrderedPresentation.ordered_uses
  intro c
  cases c with
  | inl c => exact hP c.2
  | inr c => exact hX

theorem old_divisible (P : Presentation AlgebraicComplex (Fin 2))
    (p : Ports V E) {k : ℕ} (hP : P.DegreeDivisible k) (v : V)
    (w : Fin 0 ⊕ Hidden P V E) :
    k ∣ ∑ c, ∑ j, if Sum.inr (embed P p v (P.scope c j)) = w then 1 else 0 := by
  let e : Fin 2 ⊕ Fin P.hiddenCount → Fin 0 ⊕ Hidden P V E := Sum.inr ∘ embed P p v
  have hei : Function.Injective e := Sum.inr_injective.comp (embed_injective P p v)
  by_cases hw : ∃ a, e a = w
  · obtain ⟨a,rfl⟩ := hw
    have he : (∑ c, ∑ j, if e (P.scope c j) = e a then 1 else 0) = P.degree a := by
      calc
        _ = ∑ c, ∑ j, if P.scope c j = a then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro j _
          simp only [hei.eq_iff]
        _ = P.degree a := (TwoRowRestriction.degree_sum P a).symm
    exact he.symm ▸ hP a
  · have hn : ∀ a, e a ≠ w := by simpa using hw
    change k ∣ ∑ c, ∑ j, if e (P.scope c j) = w then 1 else 0
    simp [hn]

theorem presentation_degree (P : Presentation AlgebraicComplex (Fin 2))
    (p : Ports V E) (k : ℕ) (w : Fin 0 ⊕ Hidden P V E) :
    (presentation P p k).degree (OrderedPresentation.variableEquiv w) =
      ∑ c : Tag P V E k, ∑ j, if scope P p c j = w then 1 else 0 := by
  dsimp only [presentation]
  convert OrderedPresentation.ordered_degree (arity P) (table P) (scope P p) w using 1
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

theorem divisible (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    {k : ℕ} (hP : P.DegreeDivisible k) : (compile P p k).DegreeDivisible k := by
  apply (Presentation.toInstance_divisible (presentation P p k) k).mpr
  intro w
  obtain ⟨u,rfl⟩ := (OrderedPresentation.variableEquiv
    (B := Fin 0) (H := Hidden P V E)).surjective w
  rw [presentation_degree,Fintype.sum_sum_type]
  apply dvd_add
  · simp only [Fintype.sum_prod_type]
    apply Finset.dvd_sum
    intro v _
    exact old_divisible P p hP v u
  · simp only [Fintype.sum_prod_type]
    apply Finset.dvd_sum
    intro c _
    let d : ℕ := ∑ j : Fin 2, if Sum.inr (addedScope P p c j) = u then 1 else 0
    have ht : k ∣ ∑ _ : Fin k, d := by
      rw [Finset.sum_const]
      simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      exact dvd_mul_right k d
    convert ht using 1

theorem X_power (a b : Bool) {k : ℕ} (hk : 0 < k) :
    (Signature.disequality a b : AlgebraicComplex) ^ k = Signature.disequality a b := by
  cases a <;> cases b <;> simp [Signature.disequality,Nat.ne_of_gt hk]

abbrev portAssignment (p : Ports V E) (z : E × Bool → Bool) (v : V) : Fin 4 → Bool :=
  fun i => z (p (v,i))
abbrev oldWeight (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    (z : E × Bool → Bool) (y : V × Fin P.hiddenCount → Bool) : AlgebraicComplex :=
  ∏ v, ∏ c, P.constraint c (fun j => Sum.elim
    ![z (p (v,0)),z (p (v,2))] (fun h => y (v,h)) (P.scope c j))
abbrev addedWeight (p : Ports V E) (z : E × Bool → Bool) : AlgebraicComplex :=
  (∏ v, Signature.disequality (z (p (v,0))) (z (p (v,1))) *
    Signature.disequality (z (p (v,2))) (z (p (v,3)))) *
      ∏ e, Signature.disequality (z (e,false)) (z (e,true))

theorem old_product (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    (z : E × Bool → Bool) (y : V × Fin P.hiddenCount → Bool) :
    (∏ c : V × Fin P.constraints, table P (k := 0) (Sum.inl c)
      (fun j => Sum.elim Fin.elim0 (Sum.elim z y) (scope P p (Sum.inl c) j))) =
      oldWeight P p z y := by
  rw [Fintype.prod_prod_type]
  apply Finset.prod_congr rfl
  intro v _
  apply Finset.prod_congr rfl
  intro c _
  congr 1
  funext j
  cases hs : P.scope c j with
  | inl i => fin_cases i <;> simp [scope,embed,mainPort,hs]
  | inr h => simp [scope,embed,hs]

theorem added_product (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    {k : ℕ} (hk : 0 < k) (z : E × Bool → Bool)
    (y : V × Fin P.hiddenCount → Bool) :
    (∏ c : Added V E × Fin k, table P (Sum.inr c)
      (fun j => Sum.elim Fin.elim0 (Sum.elim z y) (scope P p (Sum.inr c) j))) =
      addedWeight p z := by
  have hv (c : Added V E) (q : Fin k) :
      table P (Sum.inr (c,q))
        (fun j => Sum.elim Fin.elim0 (Sum.elim z y) (scope P p (Sum.inr (c,q)) j)) =
      kernelSignature Signature.disequality (fun j =>
        Sum.elim z y (addedScope P p c j)) := rfl
  rw [Fintype.prod_prod_type]
  simp_rw [hv]
  have hc : (Finset.univ : Finset (Fin k)).card = k := Fintype.card_fin k
  simp only [Finset.prod_const,hc,kernelSignature]
  simp_rw [X_power _ _ hk]
  simp only [Fintype.prod_sum_type,Fintype.prod_prod_type,Fin.prod_univ_two]
  rfl

theorem sum_oldWeight (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    (z : E × Bool → Bool) :
    (∑ y : V × Fin P.hiddenCount → Bool, oldWeight P p z y) =
      ∏ v, P.value ![z (p (v,0)),z (p (v,2))] := by
  let e := Equiv.curry V (Fin P.hiddenCount) Bool
  let W (v : V) (y : Fin P.hiddenCount → Bool) : AlgebraicComplex :=
    ∏ c, P.constraint c (fun j => Sum.elim ![z (p (v,0)),z (p (v,2))] y (P.scope c j))
  calc
    _ = ∑ y : V → Fin P.hiddenCount → Bool,
        oldWeight P p z (e.symm y) := (e.symm.sum_comp _).symm
    _ = ∑ y : V → Fin P.hiddenCount → Bool, ∏ v, W v (y v) := rfl
    _ = ∏ v, ∑ y : Fin P.hiddenCount → Bool, W v y := (Fintype.prod_sum W).symm
    _ = _ := by
      apply Finset.prod_congr rfl
      intro v _
      unfold Presentation.value
      refine Finset.sum_congr ?_ ?_
      · ext y
        simp only [Finset.mem_univ]
      intro y _
      rfl

theorem value (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    {g : Signature AlgebraicComplex 2} (hP : P.value = g) {k : ℕ} (hk : 0 < k) :
    (presentation P p k).value Fin.elim0 = (network p g).denote Fin.elim0 := by
  rw [presentation,OrderedPresentation.ordered_value]
  let e : (Hidden P V E → Bool) ≃ (E × Bool → Bool) × (V × Fin P.hiddenCount → Bool) :=
    Equiv.sumArrowEquivProdArrow _ _ _
  calc
    _ = ∑ q : (E × Bool → Bool) × (V × Fin P.hiddenCount → Bool),
        ∏ c : Tag P V E k, table P c
          (fun j => Sum.elim Fin.elim0 (e.symm q) (scope P p c j)) :=
      (e.symm.sum_comp _).symm
    _ = _ := by
      rw [Fintype.sum_prod_type]
      unfold FiniteNetwork.denote
      refine Finset.sum_congr ?_ ?_
      · ext z
        simp only [Finset.mem_univ]
      intro z _
      change (∑ y : V × Fin P.hiddenCount → Bool,
        ∏ c : Tag P V E k, table P c
          (fun j => Sum.elim Fin.elim0 (Sum.elim z y) (scope P p c j))) = _
      simp only [Fintype.prod_sum_type]
      simp_rw [old_product P p z,added_product P p hk z]
      rw [← Finset.sum_mul,sum_oldWeight,hP]
      have hs (v : V) (i : Fin 4) :
          Sum.elim Fin.elim0 z ((network p g).ports ⟨v,i⟩) = z (p (v,i)) := rfl
      change (∏ v, g ![z (p (v,0)),z (p (v,2))]) * addedWeight p z =
        (∏ v, Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneCore.lift g
          (fun i => Sum.elim Fin.elim0 z ((network p g).ports ⟨v,i⟩))) *
            ∏ e, Signature.disequality (z (e,false)) (z (e,true))
      simp_rw [hs,lift_product]
      simp only [addedWeight,Finset.prod_mul_distrib]
      ring

theorem partition (P : Presentation AlgebraicComplex (Fin 2)) (p : Ports V E)
    {g : Signature AlgebraicComplex 2} (hP : P.value = g) {k : ℕ} (hk : 0 < k) :
    (compile P p k).partition = (network p g).denote Fin.elim0 := by
  rw [compile,Presentation.toInstance_partition]
  rw [Fintype.sum_unique]
  convert value P p hP hk using 1
  congr 1

/-- A generated binary presentation supplies an actual finite degree-k CSP
for every closed quartic lift graph, with exact partition preservation. -/
theorem of_generated {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    {g : Signature AlgebraicComplex 2} (hg : Generated F k g) (hk : 0 < k)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (p : Ports V E) : ∃ I : Instance AlgebraicComplex,
      I.Uses F ∧ I.DegreeDivisible k ∧ I.partition = (network p g).denote Fin.elim0 := by
  obtain ⟨P,hP,hPk,hPg⟩ := hg
  exact ⟨compile P p k,uses P p k hP hX,divisible P p hPk,partition P p hPg hk⟩

end
end Paper2.DegreeCSP.QuarticLiftInstance
