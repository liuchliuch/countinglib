import Paper2.Paper1ProvedRestrictionProvider
import Paper2.FixedFieldOutput.FieldTransport
import Paper2.ExactInput.Computation.GraphReinterpretation
import Paper2.ExactInput.Computation.IndexedLanguage
import Paper2.Complexity.BellMachines.RawTripleCompile
import Paper2.Complexity.BellMachines.FixedPower
import Paper2.Tractable.Conformal.CommonBasis

/-! Actual fixed-field normalization reductions. The graph is reinterpreted
with its original ordered incidences. The conformal multiplier is corrected by
a unary edge scanner and a finite multiplication loop in one fixed number field.
Every oracle query is covered by the checked three-query controller. -/
namespace Paper2.Paper1Proved
open Computability Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.Complexity BinaryCompose FixedFieldMachines BellMachines GraphPreprocessing
open Paper2.FixedFieldOutput UniversalPairReduction.ThreeQuery
open Paper2.ExactInput.Computation
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

def edgeNumberComputes (L : Language) :
    Computes (inputEncoding L) UnaryBinary.unaryEncoding
      (fun G => G.val.edges.length) :=
  recode (RawTriple.edgesComputes.andThen (Lists.lengthUnaryComputes encodingNatBool))
    Subtype.val (fun _ => rfl) (fun _ => rfl)

/-- A genuine canonical oracle adapter with a fixed scalar for each edge.
The temporary language only chooses a common field; it is never queried. -/
theorem edgePowerReduction (L M : Language) (c : AlgebraicComplex)
    (q : Instance L → Instance M)
    (pre : Computes (inputEncoding L) (inputEncoding M) q)
    (hv : ∀ G, Problem.value .nativeX L G = c ^ G.val.edges.length * Problem.value .nativeX M (q G)) :
    FixedFieldOutput.Reduces .nativeX L M := by
  let scalar : AnySignature AlgebraicComplex := ⟨0,fun _ => c⟩
  obtain ⟨C,hC⟩ := Language.coverage_family (insert scalar M.family)
    (M.family_finite.insert scalar)
  have hMC : M.family ⊆ C.family := by rw [hC]; exact Set.subset_insert _ _
  have hcC : c ∈ C.coefficientField := by
    have hs : scalar ∈ C.family := by rw [hC]; exact Set.mem_insert _ _
    obtain ⟨i,hi⟩ := hs
    have hm := C.signature_mem_field i (fun _ => false)
    have he := congrArg (fun f : AnySignature AlgebraicComplex => f.2 (fun _ => false)) hi
    change C.signature i (fun _ => false) = c at he
    exact he ▸ hm
  let k : C.coefficientField := ⟨c,hcC⟩
  let F := C.fieldPresentation
  let into : Computes (answerEncoding M) F.encoding
      (fun v => F.decode (conversion M C v)) :=
    recode (conversionComputes M C) id (fun _ => rfl)
      (fun v => (Paper2.Algebraic.FixedField.encoding_decode F _).symm)
  let e1 := Wiring.firstComputes UnaryBinary.unaryEncoding (answerEncoding M)
  let a1 := Wiring.secondComputes UnaryBinary.unaryEncoding (answerEncoding M)
  let mult := (pairComputes (e1.andThen (powerComputes F k))
    (a1.andThen into)).andThen (fieldMultiplication F)
  let coords : Computes (pairEncoding UnaryBinary.unaryEncoding (answerEncoding M))
      (Paper2.Algebraic.vectorEncoding (Module.finrank ℚ C.coefficientField))
      (fun p => F.decode.symm (k^p.1 * F.decode (conversion M C p.2))) :=
    mult.andThen (fromFieldComputes C)
  let out := coords.andThen (TractableAlgorithms.Paper1Machine.coordinatesComputes L
    (C.coefficientField.val.toLinearMap.comp F.decode.toLinearMap))
  let ae := answerEncoding M
  let ue := UnaryBinary.unaryEncoding
  let rest := pairEncoding ae (pairEncoding ae ue)
  let first := Wiring.firstComputes ae rest
  let tail := Wiring.secondComputes ae rest
  let count := (tail.andThen (Wiring.secondComputes ae (pairEncoding ae ue))).andThen
    (Wiring.secondComputes ae ue)
  let post := (pairComputes count first).andThen out
  let prep := pairComputes pre (pairComputes pre (pairComputes pre (edgeNumberComputes L)))
  refine ⟨controlledOfEq prep post (FixedFieldOutput.outputBound .nativeX M) (answer .nativeX L) ?_⟩
  intro G
  apply Eq.symm
  apply TractableAlgorithms.Paper1Machine.coordinates_correct
  have he : conversion M C (answer .nativeX M (q G)) =
      answer .nativeX C (restrictionInput M C hMC (q G)) :=
    conversion_answer .nativeX .nativeX M C (q G)
      (restrictionInput M C hMC (q G)) (restrictionValue M C hMC (q G))
  simp only [answers, Function.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  change ((k ^ G.val.edges.length * F.decode
    (conversion M C (answer .nativeX M (q G))) : C.coefficientField) : AlgebraicComplex) = _
  rw [he]
  change C.coefficientField.subtype (k ^ G.val.edges.length * F.decode _) = _
  rw [map_mul, map_pow]
  change c ^ G.val.edges.length *
      (C.fieldPresentation.decode (answer .nativeX C
        (restrictionInput M C hMC (q G))) : AlgebraicComplex) = Problem.value .nativeX L G
  rw [answer_correct, ← restrictionValue M C hMC (q G)]
  exact (hv G).symm

def normalizationLanguage (L : Language) (D : InvertibleKernel) : Language :=
  indexedLanguage L (fun _ => D.action)

def normalizationInput (L : Language) (D : InvertibleKernel) :
    Instance L → Instance (normalizationLanguage L D) :=
  reinterpret (indexedLanguage_count L (fun _ => D.action)).symm
    (indexedLanguage_arity L (fun _ => D.action)).symm

theorem normalizationValue (L : Language) (D : InvertibleKernel)
    (c : AlgebraicComplex)
    (hc : Kernel.pullback Signature.disequality D.inverse =
      fun a b => c * Signature.disequality a b) (G : Instance L) :
    Problem.value .nativeX L G = c ^ G.val.edges.length *
      Problem.value .nativeX (normalizationLanguage L D) (normalizationInput L D G) := by
  let N := normalizationLanguage L D
  let Q := normalizationInput L D G
  have hh := reinterpret_denote
    (indexedLanguage_count L (fun _ => D.action)).symm
    (indexedLanguage_arity L (fun _ => D.action)).symm G
    L.signature N.signature
    (fun _ : Fin 1 => Signature.disequality)
    (fun _ : Fin 1 => fun a b => c * Signature.disequality a b)
    D.inverse D.matrix D.inverse_matrix
    (fun i => indexedLanguage_signature L (fun _ => D.action) i)
    (fun _ => hc.symm)
  have hscaled : (Q.val.realize Q.property N.signature
      (fun _ : Fin 1 => fun a b => c * Signature.disequality a b)).denote Fin.elim0 =
      c ^ G.val.edges.length * Problem.value .nativeX N Q := by
    simp only [Problem.value, Problem.network, Network.denote, RawClosedNetwork.realize, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    change (∑ z : (Fin G.val.edges.length × Bool) → Bool,
      (∏ v, _) * (c ^ G.val.edges.length * ∏ e, _)) = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    change _ = c ^ G.val.edges.length * ((∏ v, _) * ∏ e, Signature.disequality (z (e,false)) (z (e,true)))
    ac_rfl
  exact (congrFun hh Fin.elim0).symm.trans hscaled

theorem normalizationForward (L : Language) (D : InvertibleKernel) (hD : XConformal D)
    (M : Language) (hM : M.family = familyAction D L.family) :
    FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨c,hc,he⟩ := hD
  have hi := Conformal.pullback_inverse Signature.disequality D hc he
  let N := normalizationLanguage L D
  have hr : FixedFieldOutput.Reduces .nativeX L N := edgePowerReduction L N c⁻¹
    (normalizationInput L D)
    (sameBytesComputes L N (normalizationInput L D) (fun _ => rfl))
    (normalizationValue L D c⁻¹ hi)
  have hNM : N.family ⊆ M.family := by
    rw [hM]
    exact Set.Subset.rfl.trans_eq (indexedLanguage_family L (fun _ => D.action))
  exact hr.trans (restriction N M hNM)

theorem normalizationProvider : SourceFaithful.Paper1NormalizationAccepted := by
  constructor
  intro L _ D hD M hM
  refine ⟨?_, normalizationForward L D hD M hM⟩
  apply normalizationForward M D.symm hD.symm L
  rw [hM, Conformal.familyAction_symm_action]

end
end Paper2.Paper1Proved
