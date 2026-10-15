import ComplexCSP.Structure.MaltsevTypePinnedSplit
import ComplexCSP.Structure.WeightedMaltsevContextCompiler

/-! # Actual weighted layers from the unary-pinned class constructor

The alternate class witnesses retain the original marginal row callback at
every query. ValidLayer is established directly, so all existing exact weighted
execution lemmas apply without assuming identical old witness choices.
-/
namespace ComplexCSP.WeightedMaltsev
open MaltsevRelations MaltsevWitness ComplexityWitnessEncoding
variable {K : Type} [Field K] [DecidableEq K] {d s n : ℕ}

def buildPinnedLayer (m : Operation (Fin d)) (W : Code (Fin d) (n+1))
    (evaluate : Tuple (Fin d) (n+1) → K) (defaultValue : Fin d) : Layer K d n :=
  splitPinnedTypeClasses m (projectCode W n (Nat.le_succ n)) (rowLabel evaluate) defaultValue

/-- Correctness of the alternate actual layer; the row-equivalence assumption
is the actual structural polymorphism, not a class representation oracle. -/
theorem buildPinnedLayer_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (n+1)} (G : (Fin (n+1) → Fin d) → K)
    (hW : Correct W {x | G x ≠ 0}) (hEq : PreservesRowEquivalence m (rowFiber G))
    (evaluate : Tuple (Fin d) (n+1) → K) (he : ∀ x, evaluate x = G (view x))
    (defaultValue : Fin d) : ValidLayer G (buildPinnedLayer m W evaluate defaultValue) := by
  have hP : Correct (projectCode W n (Nat.le_succ n)) (rowSupport G) := by
    simpa only [projection_rowSupport] using projectCode_correct hW n (Nat.le_succ n)
  have hl := rowLabel_correct evaluate G he
  have hEq' : PreservesRowEquivalence m (labelFiber (rowSupport G) (rowLabel evaluate)) := by
    rw [hl,labelFiber_rowFiber]
    exact hEq
  have hR := row_equivalence_support_preserves hEq'
  constructor
  · intro e he
    have h := splitPinnedTypeClasses_correct hm hR hP (rowLabel evaluate) hEq' defaultValue e he
    simpa only [labelFiber,hl,view_ofFn,rowFiber] using h
  · intro x hx
    apply (splitPinnedTypeClasses_labels hm hR hP (rowLabel evaluate) hEq' defaultValue _).mpr
    exact ⟨x,hx,by simp only [hl,view_ofFn]⟩

/-- Literal Ω-preservation of generated complex tables supplies the exact row
congruence needed by unary-pinned class construction. -/
theorem embedded_row_equivalence (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {m : Operation (Fin d)}
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      Instance.Generated (L.mapValues σ) G → Preserves m (RowTypes.omegaRelation G).tuples)
    (G : (Fin (n+1) → Fin d) → K) (hG : Instance.Generated L G) :
    PreservesRowEquivalence m (rowFiber G) := by
  apply row_equivalence_of_omega G σ
  cases n with
  | zero => exact omega_zero_preserved _ m
  | succ n => exact hrow (n+1) (Nat.succ_pos _) _ (Instance.generated_mapValues hG σ)

/-- The pinned layer has at most d entries under the literal BO row bound. -/
theorem buildPinnedLayer_length_le {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) (n+1)} (G : (Fin (n+1) → Fin d) → K)
    (hW : Correct W {x | G x ≠ 0}) (hEq : PreservesRowEquivalence m (rowFiber G))
    (evaluate : Tuple (Fin d) (n+1) → K) (he : ∀ x, evaluate x = G (view x))
    (defaultValue : Fin d) (σ : K →+* ℂ)
    (hBO : BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows G x a))) :
    (buildPinnedLayer m W evaluate defaultValue).length ≤ d := by
  have hP : Correct (projectCode W n (Nat.le_succ n)) (rowSupport G) := by
    simpa only [projection_rowSupport] using projectCode_correct hW n (Nat.le_succ n)
  have hl := rowLabel_correct evaluate G he
  have hEq' : PreservesRowEquivalence m (labelFiber (rowSupport G) (rowLabel evaluate)) := by
    rw [hl,labelFiber_rowFiber]; exact hEq
  have hR := row_equivalence_support_preserves hEq'
  have hs := splitPinnedTypeClasses_length_le hm hR hP (rowLabel evaluate) hEq' defaultValue
    (presentLabels G) (by intro x hx; simpa only [hl,view_ofFn] using tableLabel_mem_present G x hx)
  exact hs.trans (presentLabels_card_le G σ hBO)

/-- Actual immutable-context recursion using only unary-pinned class witnesses. -/
def compilePinnedContextLayers (L : Language (Fin d) K (Fin s)) (m : Operation (Fin d))
    (defaultValue : Fin d) (g : ComplexityCSPCode.Code) :
    {n : ℕ} → StoredCode d n → List (ComplexityWeightedLayers.Layer K) → List (ComplexityWeightedLayers.Layer K)
  | 0, _, layers => layers
  | _ + 1, W, layers =>
    let evaluate := fun x => ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g (word x) layers
    let layer := buildPinnedLayer m W.toCode evaluate defaultValue
    compilePinnedContextLayers L m defaultValue g (marginalSupportCode m layer) (encodeLayer layer :: layers)

section PositiveDomain
variable [NeZero d]

theorem compilePinnedContextLayers_correct (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hs : CommonPolymorphism (generatedSupports (L.mapValues σ)) m)
    (hrow : ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n+1) → Fin d) → ℂ),
      Instance.Generated (L.mapValues σ) G → Preserves m (RowTypes.omegaRelation G).tuples)
    (defaultValue : Fin d) (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g)
    (n : ℕ) (hn : n ≤ g.vertices) (W : StoredCode d n)
    (hW : Correct W.toCode {x | ComplexityCSPMarginalBounds.marginal L g hn x ≠ 0})
    (layers : List (ComplexityWeightedLayers.Layer K)) (hrep : RepresentsMarginal L m g hn layers) :
    ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g []
      (compilePinnedContextLayers L m defaultValue g W layers) = ComplexityCSPCode.partition L g := by
  induction n generalizing layers with
  | zero =>
    have h := hrep (Vector.ofFn Fin.elim0)
    simpa [compilePinnedContextLayers,word,Vector.toList_ofFn,List.ofFn_zero,ComplexityCSPMarginalBounds.marginal_empty] using h
  | succ n ih =>
    let G := ComplexityCSPMarginalBounds.marginal L g hn
    have hG : Instance.Generated L G := generated_prefixMarginal L g hg (n+1) hn
    have hEq := embedded_row_equivalence L σ hrow G hG
    obtain ⟨hR,hTP,hclasses⟩ := embedded_row_hypotheses L σ hm hrow G hG
    let evaluate := fun x : Tuple (Fin d) (n+1) => ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g (word x) layers
    let layer := buildPinnedLayer m W.toCode evaluate defaultValue
    have hv : ValidLayer G layer := buildPinnedLayer_correct hm G hW hEq evaluate hrep defaultValue
    have heq : marginal G = ComplexityCSPMarginalBounds.marginal L g (by omega : n ≤ g.vertices) := by
      funext x
      exact (ComplexityCSPMarginalBounds.marginal_succ L g _ hn x).symm
    have hpres := embedded_support_preserves L σ hs (marginal G) (generated_marginal G hG)
    have hnext := marginalSupportCode_correct hm G layer hv hclasses hpres
    rw [heq] at hnext
    have hr := representsMarginal_prepend L hm g (by omega) hn layers hrep layer hv hclasses
    exact ih (by omega) (marginalSupportCode m layer) hnext (encodeLayer layer::layers) hr

def compileRawPinnedContextLayers (L : Language (Fin d) K (Fin s)) (m : Operation (Fin d))
    (defaultValue : Fin d) (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) :
    List (ComplexityWeightedLayers.Layer K) :=
  compilePinnedContextLayers L m defaultValue g (rawSupportWitness L m defaultValue g hg) []

/-- Genuine global BO gives the pinned constructive evaluator as a second
verified implementation, without identifying its witness choices with the first. -/
theorem jointBO_pinned_context_execution [Nonempty (Fin d)] (L : Language (Fin d) K (Fin s)) (σ : K →+* ℂ)
    (hAlg : ∀ i a, IsAlgebraic ℚ ((L.mapValues σ).value i a)) (hBO : JointBO (L.mapValues σ))
    (defaultValue : Fin d) :
    ∃ m : Operation (Fin d), IsMaltsev m ∧
      ∀ (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g),
        ComplexityWeightedLayers.execute (fun a b c => m (a,b,c)) L g []
          (compileRawPinnedContextLayers L m defaultValue g hg) = ComplexityCSPCode.partition L g := by
  obtain ⟨m,hm,hs,hrow⟩ := RowEquivalenceRealization.common_support_and_row_maltsev (L.mapValues σ) hAlg hBO
  refine ⟨m,hm,?_⟩
  intro g hg
  have htables : ∀ i, Preserves m {x | L.value i x ≠ 0} := by
    intro i
    exact embedded_support_preserves L σ hs (L.value i) (language_value_generated L i)
  have hW := rawSupportWitness_correct L hm htables defaultValue g hg
  have heq : ComplexityCSPMarginalBounds.marginal L g le_rfl = ComplexityCSPCode.eval L g := by
    funext x
    exact ComplexityCSPMarginalBounds.marginal_full L g x
  apply compilePinnedContextLayers_correct L σ hm hs hrow defaultValue g hg g.vertices le_rfl
    (rawSupportWitness L m defaultValue g hg)
  · rwa [heq]
  · exact representsMarginal_empty L m g hg

end PositiveDomain
end ComplexCSP.WeightedMaltsev
