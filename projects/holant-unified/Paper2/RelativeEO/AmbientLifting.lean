import Paper2.ExactInput.GadgetAugmentation
import Paper2.ExactInput.UnconditionalTransport
import Paper2.Paper1Accepted.Terminals

/-! Paper 2 Lemma 3.6: finite direct-gadget derivations lift to an arbitrary
larger retained language. Every step carries an actual native-X network and a
nonzero scalar. Machine reductions use only the accepted Paper 1 §2.5 direct
substitution/restriction convention and proved length-controlled composition. -/
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem

/-- The finitely many generated tables, with no assumption that they are
primitive source signatures or that a formal tensor operation is a gadget. -/
def generated (S : List (AnySignature AlgebraicComplex)) : SignatureFamily AlgebraicComplex :=
  {f | f ∈ S}

@[simp] theorem generated_nil : generated [] = ∅ := by ext f; simp [generated]
@[simp] theorem generated_cons (f : AnySignature AlgebraicComplex)
    (S : List (AnySignature AlgebraicComplex)) : generated (f :: S) = insert f (generated S) := by
  ext g
  simp [generated]

theorem realizesUpTo_mono {F G : SignatureFamily AlgebraicComplex} (hFG : F ⊆ G)
    {n : ℕ} {f : Signature AlgebraicComplex n} (h : NativeNetworkRealizesUpTo F f) :
    NativeNetworkRealizesUpTo G f := by
  obtain ⟨N, hU, hX, c, hc, hd⟩ := h
  exact ⟨N, fun v => hFG (hU v), hX, c, hc, hd⟩

/-- A finite sequence of fixed direct X-gadgets. The graph for a new table may
use earlier generated tables, but no future table, factor oracle, or Turing-only
access. Port order and scalar are present in `NativeNetworkRealizesUpTo`. -/
inductive DirectDerivation (F : SignatureFamily AlgebraicComplex) :
    List (AnySignature AlgebraicComplex) → Prop where
  | nil : DirectDerivation F []
  | adjoin {S : List (AnySignature AlgebraicComplex)}
      (prior : DirectDerivation F S) (f : AnySignature AlgebraicComplex)
      (graph : NativeNetworkRealizesUpTo (F ∪ generated S) f.2) :
      DirectDerivation F (f :: S)

/-- Exactly the same local networks work in the larger ambient resource set. -/
theorem DirectDerivation.mono {F G : SignatureFamily AlgebraicComplex} (hFG : F ⊆ G)
    {S : List (AnySignature AlgebraicComplex)} (h : DirectDerivation F S) :
    DirectDerivation G S := by
  induction h with
  | nil => exact .nil
  | adjoin prior f graph ih =>
    exact .adjoin ih f (realizesUpTo_mono (Set.union_subset_union hFG Set.Subset.rfl) graph)

/-- Closed finite induction, not an assumption of an ambient problem-level
reduction. The produced language contains exactly all original ambient tables
and generated tables; every stage is an actual length-controlled reduction. -/
theorem ambient_lifting (P : Paper1DirectGadgetAccepted) (L : Language)
    {F : SignatureFamily AlgebraicComplex} (hFL : F ⊆ L.family)
    {S : List (AnySignature AlgebraicComplex)} (h : DirectDerivation F S) :
    ∃ M : Language, M.family = L.family ∪ generated S ∧ Reduces .nativeX M L := by
  induction h with
  | nil =>
    refine ⟨L, by simp, P.directGadget_2_5 L L Set.Subset.rfl ?_⟩
    exact fun _ hf => NativeNetworkRealizesUpTo.of_mem hf
  | @adjoin S prior f graph ih =>
    obtain ⟨M, hM, hML⟩ := ih
    have hg : NativeNetworkRealizesUpTo M.family f.2 := by
      apply realizesUpTo_mono (G := M.family) _ graph
      rw [hM]
      exact Set.union_subset_union hFL Set.Subset.rfl
    obtain ⟨N, hN, hNM⟩ := P.adjoin M f.2 hg
    refine ⟨N, ?_, hNM.trans hML⟩
    rw [hN, hM, generated_cons]
    ext g
    simp only [Set.mem_insert_iff, Set.mem_union]
    tauto

/-- The same conclusion for any literal representation of the final ambient
union. Only fixed-language relabelling/restriction is invoked. -/
theorem ambient_lifting_to (P : Paper1DirectGadgetAccepted) (R : Paper1RestrictionAccepted)
    (L M : Language) {F : SignatureFamily AlgebraicComplex} (hFL : F ⊆ L.family)
    {S : List (AnySignature AlgebraicComplex)} (h : DirectDerivation F S)
    (hM : M.family = L.family ∪ generated S) : Reduces .nativeX M L := by
  obtain ⟨N, hN, hNL⟩ := ambient_lifting P L hFL h
  have hMN : M.family ⊆ N.family := by rw [hM, hN]
  exact (R.restriction_2_5 M N hMN).trans hNL

/-- Source hardness for an actual sublanguage of the derivation transfers to
the whole original ambient language. General public answer bounds discharge
nonvacuity; no extra `BoundedAnswers` assumption is requested from the caller. -/
theorem ambient_hardness (P : Paper1DirectGadgetAccepted) (R : Paper1RestrictionAccepted)
    (L H : Language) {F : SignatureFamily AlgebraicComplex} (hFL : F ⊆ L.family)
    {S : List (AnySignature AlgebraicComplex)} (h : DirectDerivation F S)
    (hH : H.family ⊆ F ∪ generated S) (hard : SharpPHard .nativeX H) :
    SharpPHard .nativeX L := by
  obtain ⟨M, hM, hML⟩ := ambient_lifting P L hFL h
  have hHM : H.family ⊆ M.family := by
    rw [hM]
    exact hH.trans (Set.union_subset_union hFL Set.Subset.rfl)
  exact hard.transport_unconditional ((R.restriction_2_5 H M hHM).trans hML)

end Paper2.RelativeEO
