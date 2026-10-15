import Paper2.RelativeEO.OccurrenceReductions
import Paper2.RelativeEO.DirectedPair
import Paper2.NetworkRealization

/-! Transparent, source-exact inputs for Paper 1 Lemmas 3.2 and 3.3, restated
as Paper 2 Lemmas 3.2 and 3.3. These fields do not supply an EO alternative,
ambient hardness, a copying context, or a nonzero closure witness. -/
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.ExactInput.Computation
open Paper2.Problem Paper2.Complexity
open scoped BigOperators

/-- The three ordered blocks A,P,Y are the disjoint summands of the literal
boundary Fin(r+(r+s)). Copies can therefore connect P to A coordinatewise,
retaining all Y blocks and making no other identifications. The step equation
is the actual native-X contraction of the g vertex into block A. -/
structure CarrierContext (L : Language) {r s : ℕ}
    (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s) where
  graph : Network AlgebraicComplex (r + (r + s))
  uses : graph.Uses L.family
  nativeX : graph.NativeX
  scalar : AlgebraicComplex
  scalar_ne_zero : scalar ≠ 0
  scalarCode : RootCode
  scalarCode_correct : scalarCode.MinimalRepresents (scalar : ℂ)
  step : ∀ (p : Fin r → Bool) (y : Fin s → Bool),
    (∑ a : Fin r → Bool, g (fun i => !(a i)) * graph.denote (Fin.append a (Fin.append p y))) =
      scalar * g p * h y

/-- The source's third premise retains an actual serialized exactly-one input,
its nonzero partition value, and an exact minimal-root code for that fixed value. -/
structure NonzeroTaggedClosure (L : Language) {r : ℕ} (g : Signature AlgebraicComplex r) where
  closedInput : TaggedInstance L g (fun k => k = 1)
  value_ne_zero : value .nativeX (tagged L g) closedInput.val ≠ 0
  code : RootCode
  code_correct : code.MinimalRepresents (value .nativeX (tagged L g) closedInput.val : ℂ)

structure Paper1OccurrenceAccepted where
  /-- Official Paper 1 Lemma 3.2; no charge, parity, EO, or nontractability promise. -/
  universalPair_3_2 : ∀ L : Language,
    TaggedReduces .nativeX L directedPair (fun k => k ≤ 1) L
  /-- Official Paper 1 Lemma 3.3, its native-X specialization. All three source
  premises are retained with actual graphs, native wires, root codes, and machines. -/
  replication_3_3 : ∀ (L : Language) (r s : ℕ)
    (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s),
    g ≠ 0 → h ≠ 0 → TaggedReduces .nativeX L g (fun k => k = 1) L →
    CarrierContext L g h → NonzeroTaggedClosure L g →
    ∀ M : Language, M.family = insert (⟨s, h⟩ : AnySignature AlgebraicComplex) L.family →
      Reduces .nativeX M L

noncomputable def directedPairClosureCertificate (L : Language) :
    NonzeroTaggedClosure L directedPair where
  closedInput := directedPairOneClosure L
  value_ne_zero := by change value _ _ (directedPairClosure L) ≠ 0; rw [directedPairClosure_value]; exact one_ne_zero
  code := rootOf 1
  code_correct := by
    change (rootOf 1).MinimalRepresents (value _ _ (directedPairClosure L) : ℂ)
    rw [directedPairClosure_value]
    exact rootOf_spec 1

/-- The source single-occurrence lemmas compose to unrestricted directed-pair
access once, and only once, an actual carrier-copying context has been proved.
The nonzero closure and restriction from ≤1 to =1 are independently proved. -/
theorem replicate_directed_pair (P : Paper1OccurrenceAccepted) (L M : Language)
    (C : CarrierContext L directedPair directedPair)
    (hM : M.family = insert (⟨2, directedPair⟩ : AnySignature AlgebraicComplex) L.family) :
    Reduces .nativeX M L :=
  P.replication_3_3 L 2 2 directedPair directedPair directedPair_ne_zero directedPair_ne_zero
    (P.universalPair_3_2 L).exactly_one C (directedPairClosureCertificate L) M hM

end Paper2.RelativeEO
