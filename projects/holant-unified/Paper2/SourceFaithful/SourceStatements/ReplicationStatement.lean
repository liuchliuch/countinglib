import Paper2.SourceFaithful.SourceStatements.ReplicationCarrier
import Paper2.SourceFaithful.SourceStatements.ReplicationPromisedTransport
import Paper2.SourceFaithful.SourceStatements.ReplicationPublicPremise
import Paper2.Paper1ProvedOccurrenceProvider

/-! Source Lemma 3.3 in both literal wire conventions. Its three premises
are an executed exactly-one reduction, a fixed copying context with the three
ordered blocks, and one actual nonzero exactly-one closure. The conclusion is
the public strict-root reduction with valid, polynomial-length oracle queries.
No classification or hardness conclusion replaces this reduction. -/
namespace Paper2.SourceFaithful.SourceStatements.Replication
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO Paper2.Problem
open Paper2.Synthesis
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def OrdinaryNonzeroTaggedClosure.toNative (L : Language) {r : ℕ}
    (g : Signature AlgebraicComplex r) (Z : OrdinaryNonzeroTaggedClosure L g) :
    NonzeroTaggedClosure (inverseKLanguage L) (sourceKBasis.symm.action g) where
  closedInput := ReplicationTransport.taggedInstanceEquiv L g (fun k => k=1) Z.closedInput
  value_ne_zero := by
    rw [ReplicationTransport.taggedInstance_value]
    exact Z.value_ne_zero
  code := Z.code
  code_correct := by
    rw [ReplicationTransport.taggedInstance_value]
    exact Z.code_correct

/-- The ordinary copying reduction executes the existing native compiler on
the unchanged incidence records, surrounded by the actual field converters.
The transformed context and closure are proved from the ordinary premises. -/
theorem ordinary_fixed (L : Language) {r s : ℕ}
    (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s)
    (one : FixedFieldOutput.TaggedReduces .ordinary L g (fun k => k=1) L)
    (C : OrdinaryCarrierContext L g h) (Z : OrdinaryNonzeroTaggedClosure L g)
    (M : Language) (hM : M.family=insert (⟨s,h⟩ : AnySignature AlgebraicComplex) L.family) :
    FixedFieldOutput.Reduces .ordinary M L := by
  have hfamily : (inverseKLanguage M).family=
      insert (⟨s,sourceKBasis.symm.action h⟩ : AnySignature AlgebraicComplex)
        (inverseKLanguage L).family := by
    rw [inverseKLanguage_family,inverseKLanguage_family,hM]
    exact Set.image_insert_eq
  have native := Paper1Proved.replication (inverseKLanguage L)
    (sourceKBasis.symm.action g) (sourceKBasis.symm.action h)
    (ReplicationTransport.ordinaryOne_to_native L g one)
    (C.toNative L g h) (Z.toNative L g) (inverseKLanguage M) hfamily
  obtain ⟨middle⟩ := native
  let first := FixedFieldOutput.sameValueReduction .ordinary .nativeX M (inverseKLanguage M)
    (inverseKInstanceEquiv M) (FixedFieldOutput.sameBytesComputes _ _ _ (fun _ => rfl))
    (fun G => (inverseKInstance_value M G).symm)
  let last := FixedFieldOutput.sameValueReduction .nativeX .ordinary (inverseKLanguage L) L
    (inverseKInstanceEquiv L).symm (FixedFieldOutput.sameBytesComputes _ _ _ (fun _ => rfl))
    (fun G => by simpa using inverseKInstance_value L ((inverseKInstanceEquiv L).symm G))
  exact ⟨first.controlledCompose (middle.controlledCompose last)⟩

/-- A native-X instance of the source copying hypothesis. -/
def CopyingContext (w : Wiring) (L : Language) {r s : ℕ}
    (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s) : Type :=
  match w with
  | .ordinary => OrdinaryCarrierContext L g h
  | .nativeX => CarrierContext L g h

/-- The third premise uses the same literal exactly-one graph in its actual
wire convention; scalar components and nullary occurrences are retained. -/
def NonzeroClosure (w : Wiring) (L : Language) {r : ℕ}
    (g : Signature AlgebraicComplex r) : Type :=
  match w with
  | .ordinary => OrdinaryNonzeroTaggedClosure L g
  | .nativeX => NonzeroTaggedClosure L g

/-- Source Lemma 3.3. The source's nonzero g,h hypotheses are explicit;
there is no arity, support, preprocessing, or nontractability restriction. -/
theorem theorem_3_3 (w : Wiring) (L : Language) {r s : ℕ}
    (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s)
    (_hg : g≠0) (_hh : h≠0)
    (one : RelativeEO.TaggedReduces w L g (fun k => k=1) L)
    (C : CopyingContext w L g h) (Z : NonzeroClosure w L g)
    (M : Language) (hM : M.family=insert (⟨s,h⟩ : AnySignature AlgebraicComplex) L.family) :
    Problem.Reduces w M L := by
  apply PublicReduction.of_fixed_field
  have fixed := public_one_to_fixed w L g one
  cases w with
  | ordinary => exact ordinary_fixed L g h fixed C Z M hM
  | nativeX => exact Paper1Proved.replication L g h fixed C Z M hM

/-- The bit read at the g end of a native wire whose context end reads a.
Identity wires retain a; X wires retain its coordinatewise complement. -/
def incomingWord {r : ℕ} (w : Wiring) (a : Fin r → Bool) : Fin r → Bool :=
  match w with
  | .ordinary => a
  | .nativeX => fun i => !(a i)

/-- A fixed algebraic context supplies its code once; no additional root-code
hypothesis or input-dependent descriptor-generation assumption is needed. -/
def contextFromGraph (w : Wiring) (L : Language) {r s : ℕ}
    (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s)
    (G : Network AlgebraicComplex (r+(r+s))) (uses : G.Uses L.family)
    (edges : ∀ e,G.edge e=w.kernel) (c : AlgebraicComplex) (hc : c≠0)
    (step : ∀ p y,(∑ a : Fin r → Bool,
      g (incomingWord w a)*G.denote (Fin.append a (Fin.append p y)))=c*g p*h y) :
    CopyingContext w L g h := by
  cases w with
  | ordinary => exact {
      graph := G, uses := uses, nativeI := edges, scalar := c, scalar_ne_zero := hc,
      scalarCode := Computation.rootOf c, scalarCode_correct := Computation.rootOf_spec c,
      step := step }
  | nativeX => exact {
      graph := G, uses := uses, nativeX := edges, scalar := c, scalar_ne_zero := hc,
      scalarCode := Computation.rootOf c, scalarCode_correct := Computation.rootOf_spec c,
      step := step }

/-- The fixed nonzero instance similarly supplies its exact code as a
constant. This constructor keeps the original exactly-one occurrence proof. -/
def closureFromInput (w : Wiring) (L : Language) {r : ℕ}
    (g : Signature AlgebraicComplex r) (J : TaggedInstance L g (fun k => k=1))
    (hne : value w (tagged L g) J.val≠0) : NonzeroClosure w L g := by
  cases w with
  | ordinary => exact {
      closedInput := J, value_ne_zero := hne,
      code := Computation.rootOf (value .ordinary (tagged L g) J.val),
      code_correct := Computation.rootOf_spec _ }
  | nativeX => exact {
      closedInput := J, value_ne_zero := hne,
      code := Computation.rootOf (value .nativeX (tagged L g) J.val),
      code_correct := Computation.rootOf_spec _ }

/-- The printed three premises of source Lemma 3.3, stated directly with the
physical ordered graph and closure, in either ordinary or native-X Holant.
Zero or nullary original rows, repeated table values, loops and parallel
edges remain in their faithful serialized records. -/
theorem theorem_3_3_literal (w : Wiring) (L : Language) {r s : ℕ}
    (g : Signature AlgebraicComplex r) (h : Signature AlgebraicComplex s)
    (hg : g≠0) (hh : h≠0)
    (one : RelativeEO.TaggedReduces w L g (fun k => k=1) L)
    (G : Network AlgebraicComplex (r+(r+s))) (uses : G.Uses L.family)
    (edges : ∀ e,G.edge e=w.kernel) (c : AlgebraicComplex) (hc : c≠0)
    (step : ∀ p y,(∑ a : Fin r → Bool,
      g (incomingWord w a)*G.denote (Fin.append a (Fin.append p y)))=c*g p*h y)
    (J : TaggedInstance L g (fun k => k=1)) (hne : value w (tagged L g) J.val≠0)
    (M : Language) (hM : M.family=insert (⟨s,h⟩ : AnySignature AlgebraicComplex) L.family) :
    Problem.Reduces w M L :=
  theorem_3_3 w L g h hg hh one
    (contextFromGraph w L g h G uses edges c hc step) (closureFromInput w L g J hne) M hM


end
end Paper2.SourceFaithful.SourceStatements.Replication
