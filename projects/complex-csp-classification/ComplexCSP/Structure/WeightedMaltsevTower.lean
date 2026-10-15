import ComplexCSP.Structure.WeightedMaltsevMachineBridge

/-! # Computed layer towers and agreement with the actual FP layer executor -/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness
open ComplexityWitnessEncoding
open scoped BigOperators
variable {K : Type} [Field K] [DecidableEq K] {d s : ℕ}

inductive LayerTower (K : Type) (d : ℕ) : ℕ → Type
  | empty : LayerTower K d 0
  | extend {n : ℕ} : LayerTower K d n → Layer K d n → LayerTower K d (n + 1)

def ValidTower (m : Operation (Fin d)) : {n : ℕ} → ((Fin n → Fin d) → K) → LayerTower K d n → Prop
  | 0, _, .empty => True
  | _ + 1, G, .extend T layer =>
    ValidLayer G layer ∧ (∀ a, Preserves m (rowFiber G a)) ∧ ValidTower m (marginal G) T

def compileTower (m : Operation (Fin d)) (defaultValue : Fin d) :
    {n : ℕ} → (Tuple (Fin d) n → K) → StoredCode d n → LayerTower K d n
  | 0, _, _ => .empty
  | _ + 1, evaluate, W =>
    let layer := buildLayer m W.toCode evaluate defaultValue
    .extend (compileTower m defaultValue (evaluateLayer m layer evaluate) (marginalSupportCode m layer)) layer

theorem compileTower_valid (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (generatedSupports (L.mapValues σ)) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n + 1) → Fin d) → ℂ),
      Instance.Generated (L.mapValues σ) G → Preserves m (RowTypes.omegaRelation G).tuples)
    (defaultValue : Fin d) (n : ℕ) (G : (Fin n → Fin d) → K)
    (hG : Instance.Generated L G) (W : StoredCode d n) (hW : Correct W.toCode {x | G x ≠ 0})
    (evaluate : Tuple (Fin d) n → K) (he : ∀ x, evaluate x = G (view x)) :
    ValidTower m G (compileTower m defaultValue evaluate W) := by
  induction n with
  | zero => trivial
  | succ n ih =>
    obtain ⟨hR, hTP, hclasses⟩ := embedded_row_hypotheses L σ hm hrow G hG
    let layer := buildLayer m W.toCode evaluate defaultValue
    have hv : ValidLayer G layer := buildLayer_correct hm G hW hR hTP hclasses evaluate he defaultValue
    have hM := generated_marginal G hG
    have hpres := embedded_support_preserves L σ hs (marginal G) hM
    have hnext := marginalSupportCode_correct hm G layer hv hclasses hpres
    exact ⟨hv, hclasses, ih (marginal G) hM (marginalSupportCode m layer) hnext
      (evaluateLayer m layer evaluate) (evaluateLayer_correct hm G layer hv hclasses evaluate he)⟩

def encodeTower : {n : ℕ} → LayerTower K d n → List (ComplexityWeightedLayers.Layer K)
  | 0, .empty => []
  | _ + 1, .extend T layer => encodeTower T ++ [encodeLayer layer]

omit [DecidableEq K] in
@[simp] theorem encodeTower_length {n : ℕ} (T : LayerTower K d n) : (encodeTower T).length = n := by
  induction T with
  | empty => rfl
  | extend T layer ih => simp [encodeTower, ih]

section PositiveDomain
variable [NeZero d]

def walkTower (m : Operation (Fin d)) : {n : ℕ} → LayerTower K d n → Tuple (Fin d) n × List K
  | 0, .empty => (Vector.ofFn Fin.elim0, [])
  | _ + 1, .extend T layer =>
    let previous := walkTower m T
    let choice := chooseRow m layer previous.1
    (snocTuple previous.1 choice.1, previous.2 ++ [choice.2])

omit [DecidableEq K] in
theorem execute_walkTower (m : Operation (Fin d)) {n : ℕ} (T : LayerTower K d n) :
    (encodeTower T).foldl (ComplexityWeightedLayers.step (fun a b c => m (a,b,c))) ([], []) =
      (word (walkTower m T).1, (walkTower m T).2) := by
  induction T with
  | empty => simp [encodeTower, walkTower, word]
  | extend T layer ih =>
    simp only [encodeTower, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, walkTower]
    exact step_encode m (walkTower m T).1 (walkTower m T).2 layer

/-- Exact product of the selected factors, including zero-factor fallback.
No growth premise is needed: factors are copied from the actual layer data. -/
theorem walkTower_factor {m : Operation (Fin d)} (hm : IsMaltsev m)
    {n : ℕ} (T : LayerTower K d n) (G : (Fin n → Fin d) → K) (hv : ValidTower m G T) :
    (∑ x, G x) = G (view (walkTower m T).1) * (walkTower m T).2.prod := by
  induction T with
  | empty =>
    simp only [walkTower, List.prod_nil, mul_one, view_ofFn, Fintype.sum_unique]
    exact congrArg G (Subsingleton.elim _ _)
  | extend T layer ih =>
    have hlower := ih (marginal G) hv.2.2
    have hchoice := chooseRow_factor hm G layer hv.1 hv.2.1 (walkTower m T).1
    rw [← sum_marginal G, hlower, hchoice]
    simp only [walkTower, List.prod_append, List.prod_singleton]
    ring

/-- The already-compiled raw executor agrees with the mathematical layer tower
for the literal original instance, with no terminal evaluation oracle. -/
theorem execute_encodedTower (L : Language (Fin d) K (Fin s))
    {m : Operation (Fin d)} (hm : IsMaltsev m) (g : ComplexityCSPCode.Code)
    (hg : ComplexityCSPCode.Valid L g) (T : LayerTower K d g.vertices)
    (hv : ValidTower m (ComplexityCSPCode.eval L g) T) :
    ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g [] (encodeTower T) =
      ComplexityCSPCode.partition L g := by
  simp only [ComplexityWeightedLayers.execute, execute_walkTower, ComplexityWeightedLayers.finish]
  rw [ComplexityCSPWordAssignment.assignmentWeight_tuple_eq L g hg]
  exact (walkTower_factor hm T (ComplexityCSPCode.eval L g) hv).symm

def compileRawLayers (L : Language (Fin d) K (Fin s)) (m : Operation (Fin d)) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) : List (ComplexityWeightedLayers.Layer K) :=
  encodeTower (compileTower m defaultValue (fun x => ComplexityCSPCode.eval L g (view x))
    (rawSupportWitness L m defaultValue g hg))

/-- Concrete layer construction followed by the actual FP execution machine
computes every partition value under the original global hypotheses. The FP
compilation of the layer constructor itself remains a separate obligation. -/
theorem jointBO_compiled_execution [Nonempty (Fin d)] (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    (hAlg : ∀ i a, IsAlgebraic ℚ ((L.mapValues σ).value i a)) (hBO : JointBO (L.mapValues σ))
    (defaultValue : Fin d) :
    ∃ m : Operation (Fin d), IsMaltsev m ∧
      ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g),
        ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g []
          (compileRawLayers L m defaultValue g hg) = ComplexityCSPCode.partition L g := by
  obtain ⟨m, hm, hs, hrow⟩ := RowEquivalenceRealization.common_support_and_row_maltsev (L.mapValues σ) hAlg hBO
  refine ⟨m, hm, ?_⟩
  intro g hg
  have htables : ∀ i, Preserves m {x | L.value i x ≠ 0} := by
    intro i
    exact embedded_support_preserves L σ hs (L.value i) (language_value_generated L i)
  apply execute_encodedTower L hm g hg
  exact compileTower_valid L σ hm hs hrow defaultValue g.vertices (ComplexityCSPCode.eval L g)
    (raw_assignment_generated L g hg) (rawSupportWitness L m defaultValue g hg)
    (rawSupportWitness_correct L hm htables defaultValue g hg) _ (fun _ => rfl)

end PositiveDomain
end ComplexCSP.WeightedMaltsev
