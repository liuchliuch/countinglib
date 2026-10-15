import ComplexCSP.Structure.WeightedMaltsevStructure
import ComplexCSP.Structure.MaltsevCSPGlobal
import ComplexCSP.Structure.StructuralCollapse

/-!
# Actual recursive weighted elimination

Every support, row label and class representation is computed by the algorithms
already proved. The evaluator is initialized by the literal raw assignment
product, not by a variable-arity function oracle. This module establishes exact
values; bit-machine polynomial time is a separate compilation obligation.
-/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness
open scoped BigOperators
variable {K : Type} [Field K] [DecidableEq K] {d s : ℕ}

def eliminate (m : Operation (Fin d)) (defaultValue : Fin d) :
    {n : ℕ} → (Tuple (Fin d) n → K) → StoredCode d n → K
  | 0, evaluate, _ => evaluate (Vector.ofFn Fin.elim0)
  | _ + 1, evaluate, W =>
    let layer := buildLayer m W.toCode evaluate defaultValue
    let nextW := marginalSupportCode m layer
    eliminate m defaultValue (evaluateLayer m layer evaluate) nextW

def splitLastScope (n : ℕ) : Fin (n + 1) → Fin n ⊕ Fin 1 :=
  Fin.lastCases (Sum.inr 0) (fun i => Sum.inl i)

theorem splitLast_assignment (n : ℕ) (x : Fin n → Fin d) (a : Fin 1 → Fin d) :
    Sum.elim x a ∘ splitLastScope n = Fin.snoc x (a 0) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [splitLastScope]

omit [DecidableEq K] in
theorem generated_marginal {L : Language (Fin d) K (Fin s)} {n : ℕ}
    (G : (Fin (n + 1) → Fin d) → K) (hG : Instance.Generated L G) :
    Instance.Generated L (marginal G) := by
  have hrename := Instance.generated_diagonal_minor hG (splitLastScope n)
  have hsum := Instance.generated_marginal (B := Fin n) (H := Fin 1) hrename
  convert hsum using 1
  funext x
  simp only [marginal, splitLast_assignment]
  exact ((Equiv.funUnique (Fin 1) (Fin d)).sum_comp (fun a => G (Fin.snoc x a))).symm

def snocEquiv (n d : ℕ) : ((Fin n → Fin d) × Fin d) ≃ (Fin (n + 1) → Fin d) where
  toFun p := Fin.snoc p.1 p.2
  invFun x := (Fin.init x, x (Fin.last n))
  left_inv p := by rcases p with ⟨x, a⟩; simp
  right_inv x := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [Fin.init]

omit [DecidableEq K] in
theorem sum_marginal {n : ℕ} (G : (Fin (n + 1) → Fin d) → K) :
    (∑ x, marginal G x) = ∑ x, G x := by
  have h := (snocEquiv n d).sum_comp G
  change (∑ p : (Fin n → Fin d) × Fin d, G (Fin.snoc p.1 p.2)) = ∑ x, G x at h
  rw [Fintype.sum_prod_type] at h
  change (∑ x, ∑ a, G (Fin.snoc x a)) = ∑ x, G x
  exact h

omit [DecidableEq K] in
theorem embedded_support_preserves (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {m : Operation (Fin d)} (hs : CommonPolymorphism (generatedSupports (L.mapValues σ)) m)
    {n : ℕ} (G : (Fin n → Fin d) → K) (hG : Instance.Generated L G) :
    Preserves m {x | G x ≠ 0} := by
  have hG' := Instance.generated_mapValues hG σ
  let R : Relation (Fin d) := ⟨n, {x | σ (G x) ≠ 0}⟩
  have h := hs R ⟨_, hG', rfl⟩
  simpa only [R, map_ne_zero] using h

theorem embedded_row_hypotheses (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n + 1) → Fin d) → ℂ),
      Instance.Generated (L.mapValues σ) G → Preserves m (RowTypes.omegaRelation G).tuples)
    {n : ℕ} (G : (Fin (n + 1) → Fin d) → K) (hG : Instance.Generated L G) :
    Preserves m (rowSupport G) ∧ AllTypesPartition (rowSupport G) (fun x => tableLabel G (view x)) ∧
      ∀ a, Preserves m (rowFiber G a) := by
  apply omega_supplies_layer_hypotheses G σ hm
  cases n with
  | zero => exact omega_zero_preserved _ m
  | succ n => exact hrow (n + 1) (Nat.succ_pos _) _ (Instance.generated_mapValues hG σ)

/-- Exact partition evaluation by the concrete recursive compiler. -/
theorem eliminate_correct (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (generatedSupports (L.mapValues σ)) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n + 1) → Fin d) → ℂ),
      Instance.Generated (L.mapValues σ) G → Preserves m (RowTypes.omegaRelation G).tuples)
    (defaultValue : Fin d) (n : ℕ) (G : (Fin n → Fin d) → K)
    (hG : Instance.Generated L G) (W : StoredCode d n) (hW : Correct W.toCode {x | G x ≠ 0})
    (evaluate : Tuple (Fin d) n → K) (he : ∀ x, evaluate x = G (view x)) :
    eliminate m defaultValue evaluate W = ∑ x, G x := by
  induction n with
  | zero =>
    change evaluate (Vector.ofFn Fin.elim0) = _
    rw [he]
    simp only [view_ofFn, Fintype.sum_unique]
    exact congrArg G (Subsingleton.elim _ _)
  | succ n ih =>
    obtain ⟨hR, hTP, hclasses⟩ := embedded_row_hypotheses L σ hm hrow G hG
    let layer := buildLayer m W.toCode evaluate defaultValue
    have hv : ValidLayer G layer := buildLayer_correct hm G hW hR hTP hclasses evaluate he defaultValue
    have hM := generated_marginal G hG
    have hpres := embedded_support_preserves L σ hs (marginal G) hM
    have hnext := marginalSupportCode_correct hm G layer hv hclasses hpres
    have hresult := ih (marginal G) hM (marginalSupportCode m layer) hnext
      (evaluateLayer m layer evaluate) (evaluateLayer_correct hm G layer hv hclasses evaluate he)
    exact hresult.trans (sum_marginal G)

omit [DecidableEq K] in
/-- The raw instance's full assignment table has a literal generated witness
with all its variables exposed and no hidden variables. -/
theorem raw_assignment_generated (L : Language (Fin d) K (Fin s))
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) :
    Instance.Generated L (ComplexityCSPCode.eval L g) := by
  let I : Instance L (Fin g.vertices) (Fin 0) :=
    ⟨g.constraints.attach.map fun c =>
      ⟨⟨c.val.1, (hg c.val c.property).choose⟩,
        fun i => Sum.inl (ComplexityCSPCode.scope L g c.val (hg c.val c.property) i)⟩⟩
  refine ⟨0, I, ?_⟩
  intro x
  have he : I.eval x Fin.elim0 = ComplexityCSPCode.eval L g x := by
    calc
      _ = (ComplexityCSPCode.toInstance L g hg).eval Fin.elim0 x := by
        simp [I, Instance.eval, Constraint.eval, ComplexityCSPCode.toInstance, Function.comp_def]
      _ = _ := ComplexityCSPCode.eval_toInstance L g hg x
  rw [Instance.partition, Fintype.sum_unique]
  exact (congrArg (I.eval x)
    (Subsingleton.elim (default : Fin 0 → Fin d) Fin.elim0)).trans he

def evaluateRaw (L : Language (Fin d) K (Fin s)) (m : Operation (Fin d)) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) : K :=
  eliminate m defaultValue (fun x => ComplexityCSPCode.eval L g (view x))
    (rawSupportWitness L m defaultValue g hg)

/-- The source's global condition yields one fixed operation for which the
actual evaluator computes every valid raw instance's exact partition value. -/
theorem jointBO_exact_evaluator [Nonempty (Fin d)] (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    (hAlg : ∀ i a, IsAlgebraic ℚ ((L.mapValues σ).value i a)) (hBO : JointBO (L.mapValues σ))
    (defaultValue : Fin d) :
    ∃ m : Operation (Fin d), IsMaltsev m ∧
      ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g),
        evaluateRaw L m defaultValue g hg = ComplexityCSPCode.partition L g := by
  obtain ⟨m, hm, hs, hrow⟩ := RowEquivalenceRealization.common_support_and_row_maltsev (L.mapValues σ) hAlg hBO
  refine ⟨m, hm, ?_⟩
  intro g hg
  have htables : ∀ i, Preserves m {x | L.value i x ≠ 0} := by
    intro i
    exact embedded_support_preserves L σ hs (L.value i) (language_value_generated L i)
  exact eliminate_correct L σ hm hs hrow defaultValue g.vertices (ComplexityCSPCode.eval L g)
    (raw_assignment_generated L g hg) (rawSupportWitness L m defaultValue g hg)
    (rawSupportWitness_correct L hm htables defaultValue g hg) _ (fun _ => rfl)

end ComplexCSP.WeightedMaltsev
