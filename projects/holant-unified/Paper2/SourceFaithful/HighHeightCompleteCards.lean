import Paper2.SourceFaithful.HighHeightCompleteFactorAccess
import Paper2.HighHeightNormalization.CardNetwork
import Paper2.HighHeightNormalization.FactorParameters
import Paper2.RelativeEO.ARSFactors

/-! Finite retained access to the actual contraction cards and their ordered
ARS factors.  Source graph semantics, field coefficients, charge promises and
both directions of the oracle reduction are retained at every stage. -/
namespace Paper2.SourceFaithful.HighHeight
set_option backward.isDefEq.respectTransparency false
open Tractable ExactInput Paper2.RelativeEO
open Paper2.HighHeightNormalization MatchingPropagation CommonPhase EndpointSelfLoop

noncomputable instance portPairFintype {ι : Type} [Fintype ι] : Fintype (PortPair ι) :=
  Fintype.ofInjective (fun e : PortPair ι => (e.first,e.second)) (by
    intro e f h
    cases e
    cases f
    simp only [Prod.mk.injEq] at h
    rcases h with ⟨rfl,rfl⟩
    rfl)

/-- A retained normalization stage.  Charge constraints are on all literal
members of the target language, including the newly extracted binaries. -/
structure RetainedStage (L : Language) (d : ℕ) where
  language : Language
  contains : L.family ⊆ language.family
  preprocessed : Preprocessed language.family
  even : ∀ g ∈ language.family, Even g.1
  divisible : ∀ g ∈ language.family, Tensor.HalfChargeDivisible g.2 d
  backward : FixedFieldOutput.Reduces .nativeX language L
  forward : FixedFieldOutput.Reduces .nativeX L language

theorem realizable_mono {K ι : Type} [CommSemiring K]
    {F G : SignatureFamily K} (hFG : F ⊆ G) {f : Tensor K ι}
    (hf : NetworkRealizable F f) : NetworkRealizable G f := by
  obtain ⟨n,N,e,hU,hX,hN⟩ := hf
  exact ⟨n,N,e,(fun v => hFG (hU v)),hX,hN⟩

namespace RetainedStage
def refl (R : Paper1RestrictionAccepted) (L : Language) (d : ℕ)
    (hpre : Preprocessed L.family)
    (heven : ∀ g ∈ L.family, Even g.1)
    (hdiv : ∀ g ∈ L.family, Tensor.HalfChargeDivisible g.2 d) : RetainedStage L d :=
  ⟨L,(fun _ h => h),hpre,heven,hdiv,
    R.restriction_2_5 L L (Set.Subset.refl _),
    R.restriction_2_5 L L (Set.Subset.refl _)⟩

def trans {L : Language} {d : ℕ} (S : RetainedStage L d)
    (T : RetainedStage S.language d) : RetainedStage L d :=
  ⟨T.language,(fun g hg => T.contains (S.contains hg)),T.preprocessed,T.even,T.divisible,
    T.backward.trans S.backward,S.forward.trans T.forward⟩

theorem not_oneSided {L : Language} {d : ℕ} (S : RetainedStage L d)
    (h : ¬ CommonOneSided L.family) : ¬ CommonOneSided S.language.family := by
  intro hs
  apply h
  rcases hs with hs | hs
  · exact Or.inl (fun g hg => hs g (S.contains hg))
  · exact Or.inr (fun g hg => hs g (S.contains hg))

theorem nontractable {L : Language} {d : ℕ} (S : RetainedStage L d)
    (h : ¬ Tract (kImage L)) : ¬ Tract (kImage S.language) :=
  Paper2.HeightThree.retained_nontractable L S.language S.contains h
end RetainedStage

/-- Access means one actual algebraic binary graph, with its coefficient
embedding explicitly identified. -/
def AvailableBinary (L : Language) (z : ℂ) : Prop :=
  ∃ a : AlgebraicComplex, (a : ℂ) = z ∧
    NetworkRealizable L.family (binaryTable (algebraicBinary a))

theorem binaryTable_eoSignature (a : AlgebraicComplex) :
    binaryTable (algebraicBinary a) = eoSignature a (conjugateAlgebraic a) := by
  funext x
  cases x 0 <;> cases x 1 <;> rfl

/-- Reversing the two literal ports makes B(conj z), so conjugating a chosen
parameter uses an actual ordered copy of the available binary graph. -/
theorem availableBinary_star (L : Language) (z : ℂ)
    (h : AvailableBinary L z) : AvailableBinary L (star z) := by
  obtain ⟨a,ha,hr⟩ := h
  refine ⟨conjugateAlgebraic a,by simpa only [coe_conjugateAlgebraic,ha],?_⟩
  have he : Tensor.reindex (Equiv.swap (0 : Fin 2) 1)
      (binaryTable (algebraicBinary a)) = binaryTable (algebraicBinary (conjugateAlgebraic a)) := by
    funext x
    simp only [Tensor.reindex_apply,Equiv.swap_apply_left,Equiv.swap_apply_right]
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [binaryTable,algebraicBinary,WeightedMatching.binary,h0,h1]
    all_goals apply Subtype.ext; simp [conjugateAlgebraic]
  exact he ▸ hr.reindex _

theorem availableBinary_mono {L N : Language} (hLN : L.family ⊆ N.family)
    {z : ℂ} (hz : AvailableBinary L z) : AvailableBinary N z := by
  obtain ⟨a,ha,hr⟩ := hz
  exact ⟨a,ha,realizable_mono hLN hr⟩

theorem cardTable_nonzero_complex {n : ℕ} (M : Signature AlgebraicComplex n)
    (e : PortPair (Fin n)) :
    cardTable M e ≠ 0 ↔ contraction (fun x => (M x : ℂ)) e ≠ 0 := by
  have hcoe : (fun x => (cardTable M e x : ℂ)) ≠ 0 ↔ cardTable M e ≠ 0 := by
    constructor
    · intro h hz
      apply h
      funext x
      rw [hz]
      rfl
    · intro h hz
      apply h
      funext x
      exact Subtype.ext (congrFun hz x)
  rw [← hcoe,cardTable_coe,cardTable_nonzero]

theorem isARS_reindex {ι κ : Type} {f : Tensor ℂ ι}
    (h : IsARS f) (e : ι ≃ κ) : IsARS (Tensor.reindex e f) := by
  obtain ⟨P,z,c,hc,hz,hf⟩ := h
  exact ⟨⟨P.count,P.ports.trans e⟩,z,c,hc,hz,by rw [hf]; rfl⟩

theorem ars_cardTable_ars {n : ℕ} (M : Signature AlgebraicComplex n)
    (e : PortPair (Fin n)) (h : IsARSProduct (cardTable M e)) :
    IsARS (contraction (fun x => (M x : ℂ)) e) := by
  have hh := isARS_reindex h.coe (Fintype.equivFin (Remaining e.first e.second)).symm
  have he : Tensor.reindex (Fintype.equivFin (Remaining e.first e.second)).symm
      (fun x => (cardTable M e x : ℂ)) = contraction (fun x => (M x : ℂ)) e := by
    rw [cardTable_coe]
    funext x
    simp [cardTable,Tensor.reindex]
  exact he ▸ hh

/-- Adjoin one nonzero actual EO output without changing any original
signature.  All source-language invariants and both oracle directions hold. -/
theorem adjoin_eo_stage (G : Paper1DirectGadgetAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) {d n : ℕ} (hpre : Preprocessed L.family)
    (heven : ∀ g ∈ L.family, Even g.1)
    (hdiv : ∀ g ∈ L.family, Tensor.HalfChargeDivisible g.2 d)
    (f : Signature AlgebraicComplex n) (hn : 0 < n) (hf : f ≠ 0)
    (heo : IsEO (⟨n,f⟩ : AnySignature AlgebraicComplex))
    (hr : NetworkRealizable L.family f) :
    ∃ S : RetainedStage L d, (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ S.language.family := by
  obtain ⟨N,hN,hNL⟩ := G.adjoin_realizable L f hr
  have hLN : L.family ⊆ N.family := by rw [hN]; exact Set.subset_insert _ _
  refine ⟨⟨N,hLN,?_,?_,?_,hNL,R.restriction_2_5 L N hLN⟩,?_⟩
  · rw [hN]
    exact Paper2.HeightThree.insert_nonzero_positive_preprocessed _ _ hn hf hpre
  · rw [hN]
    exact Paper2.HeightThree.insert_eo_even _ _ heo heven
  · rw [hN]
    exact Paper2.HeightThree.insert_eo_halfCharge_divisible _ _ heo d hdiv
  · rw [hN]
    exact Set.mem_insert _ _

/-- Factor access for one actual nonzero EO card.  The precise ordered
algebraic parameters are preserved, and all of their attaching graphs become
available in a finite equivalent language. -/
theorem realized_ars_factors_stage
    (G : Paper1DirectGadgetAccepted) (F : Paper1FactorClosureAccepted)
    (R : Paper1RestrictionAccepted) (L : Language) {d n : ℕ}
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (heven : ∀ g ∈ L.family, Even g.1)
    (hdiv : ∀ g ∈ L.family, Tensor.HalfChargeDivisible g.2 d)
    (f : Signature AlgebraicComplex n) (hn : 0 < n) (hf : f ≠ 0)
    (heo : IsEO (⟨n,f⟩ : AnySignature AlgebraicComplex))
    (hr : NetworkRealizable L.family f) (hars : IsARSProduct f) :
    ∃ (S : RetainedStage L d) (P : OrientedPerfectPairing n)
      (z : Fin P.count → AlgebraicComplex) (c : AlgebraicComplex),
      c ≠ 0 ∧ (∀ j, z j ≠ 0) ∧
      f = WeightedMatching.product P z (fun j => conjugateAlgebraic (z j)) c ∧
      (∀ j, AvailableBinary S.language (z j : ℂ)) := by
  obtain ⟨S,hfmem⟩ := adjoin_eo_stage G R L hpre heven hdiv f hn hf heo hr
  obtain ⟨P,z,c,N,hc,hz,hform,_,hSN,hfac,hpreN,_,_,_,hevenN,hdivN,hNS,hSN'⟩ :=
    ars_factors_retained F R S.language S.preprocessed (S.not_oneSided htwo) f hfmem hars
  let T : RetainedStage S.language d :=
    ⟨N,hSN,hpreN,hevenN S.even,hdivN d S.divisible,hNS,hSN'⟩
  refine ⟨S.trans T,P,z,c,hc,hz,hform,?_⟩
  intro j
  refine ⟨z j,rfl,?_⟩
  rw [binaryTable_eoSignature]
  exact supplied_realizable (hfac j)

/-- An accessible ARS witness retains the literal undeleted port subtype,
the original exact algebraic parameters and the entire coefficient formula. -/
structure CardWitness (L : Language) {n : ℕ}
    (M : Signature AlgebraicComplex n) (e : PortPair (Fin n)) where
  pairing : Matching (Remaining e.first e.second)
  parameter : Fin pairing.count → AlgebraicComplex
  scalar : AlgebraicComplex
  scalar_ne_zero : scalar ≠ 0
  parameter_ne_zero : ∀ j, parameter j ≠ 0
  coefficient : contraction (fun x => (M x : ℂ)) e =
    product pairing (fun j => (parameter j : ℂ)) (fun j => star (parameter j : ℂ)) (scalar : ℂ)
  available : ∀ j, AvailableBinary L (parameter j : ℂ)

def CardWitness.mono {L N : Language} (hLN : L.family ⊆ N.family)
    {n : ℕ} {M : Signature AlgebraicComplex n} {e : PortPair (Fin n)}
    (W : CardWitness L M e) : CardWitness N M e :=
  { W with available := fun j => availableBinary_mono hLN (W.available j) }

/-- Undo the exact boundary enumeration of an ordered contraction card.
No complex representative or new coefficient field is chosen. -/
noncomputable def cardWitness_of_ordered {L : Language} {n : ℕ}
    (M : Signature AlgebraicComplex n) (e : PortPair (Fin n))
    (P : OrientedPerfectPairing (Fintype.card (Remaining e.first e.second)))
    (z : Fin P.count → AlgebraicComplex) (c : AlgebraicComplex)
    (hc : c ≠ 0) (hz : ∀ j, z j ≠ 0)
    (hform : cardTable M e = WeightedMatching.product P z
      (fun j => conjugateAlgebraic (z j)) c)
    (ha : ∀ j, AvailableBinary L (z j : ℂ)) : CardWitness L M e := by
  let E := Fintype.equivFin (Remaining e.first e.second)
  let Q : Matching (Remaining e.first e.second) := ⟨P.count,P.ports.trans E.symm⟩
  refine ⟨Q,z,c,hc,hz,?_,ha⟩
  funext x
  have h := congrFun hform (fun i => x (E.symm i))
  have h' := congrArg (fun a : AlgebraicComplex => (a : ℂ)) h
  have hleft : (cardTable M e (fun i => x (E.symm i)) : ℂ) =
      contraction (fun y => (M y : ℂ)) e x := by
    have hh := congrFun (cardTable_coe M e) (fun i => x (E.symm i))
    exact hh.trans (by simp [cardTable,Tensor.reindex,E])
  rw [hleft] at h'
  have hright : (WeightedMatching.product (K := AlgebraicComplex) P z (fun j => conjugateAlgebraic (z j)) c
      (fun i => x (E.symm i)) : ℂ) =
      product Q (fun j => (z j : ℂ)) (fun j => star (z j : ℂ)) (c : ℂ) x := by
    let φ : AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom
    change φ (c * ∏ j,WeightedMatching.binary (z j) (conjugateAlgebraic (z j))
      (x (Q.ports (j,false))) (x (Q.ports (j,true)))) = _
    rw [map_mul,map_prod]
    change (c : ℂ) * _ = (c : ℂ) * _
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    change φ (WeightedMatching.binary (z j) (conjugateAlgebraic (z j))
      (x (Q.ports (j,false))) (x (Q.ports (j,true)))) =
      WeightedMatching.binary (z j : ℂ) (star (z j : ℂ))
        (x (Q.ports (j,false))) (x (Q.ports (j,true)))
    cases x (Q.ports (j,false)) <;> cases x (Q.ports (j,true)) <;> rfl
  exact h'.trans hright

/-- A literal nonzero contraction card can be supplied and its ARS factors
extracted in a finite retained stage over the same source family. -/
theorem contraction_factors_stage
    (G : Paper1DirectGadgetAccepted) (F : Paper1FactorClosureAccepted)
    (R : Paper1RestrictionAccepted) (L : Language) {d : ℕ}
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (heven : ∀ g ∈ L.family, Even g.1)
    (hdiv : ∀ g ∈ L.family, Tensor.HalfChargeDivisible g.2 d)
    (M : Signature AlgebraicComplex (2*d))
    (hM : NetworkRealizable L.family M) (e : PortPair (Fin (2*d)))
    (hn : 0 < Fintype.card (Remaining e.first e.second))
    (hf : cardTable M e ≠ 0) (hars : IsARSProduct (cardTable M e)) :
    ∃ S : RetainedStage L d, Nonempty (CardWitness S.language M e) := by
  have heo : IsEO (⟨Fintype.card (Remaining e.first e.second),cardTable M e⟩ :
      AnySignature AlgebraicComplex) := by
    have hc := cardTable_arity e
    refine ⟨⟨d-1,?_⟩,?_⟩
    · change Fintype.card (Remaining e.first e.second) = 2*(d-1)
      omega
    · exact (centralSupport_iff_chargeLayer _).mpr
        (cardTable_chargeLayer M e (fun g hg => ⟨heven g hg,hdiv g hg⟩) hM)
  obtain ⟨S,P,z,c,hc,hz,hform,ha⟩ := realized_ars_factors_stage G F R L hpre htwo
    heven hdiv (cardTable M e) hn hf heo (cardTable_realizable M e hM) hars
  exact ⟨S,⟨cardWitness_of_ordered M e P z c hc hz hform ha⟩⟩

/-- Only finitely many cards are processed.  All selected factors coexist in
one retained exact-input language, and no unrelated prime factor is retained.
The ARS hypothesis concerns the actual original coefficient cards only. -/
theorem finite_contraction_factors_stage
    (G : Paper1DirectGadgetAccepted) (F : Paper1FactorClosureAccepted)
    (R : Paper1RestrictionAccepted) (L : Language) {d : ℕ}
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (heven : ∀ g ∈ L.family, Even g.1)
    (hdiv : ∀ g ∈ L.family, Tensor.HalfChargeDivisible g.2 d)
    (M : Signature AlgebraicComplex (2*d))
    (hM : NetworkRealizable L.family M)
    (s : Finset (PortPair (Fin (2*d))))
    (hpositive : ∀ e ∈ s, 0 < Fintype.card (Remaining e.first e.second))
    (hars : ∀ e ∈ s, cardTable M e ≠ 0 → IsARSProduct (cardTable M e)) :
    ∃ S : RetainedStage L d,
      ∀ e ∈ s, cardTable M e ≠ 0 → Nonempty (CardWitness S.language M e) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨⟨L,(fun _ h => h),hpre,heven,hdiv,
        R.restriction_2_5 L L (Set.Subset.refl _),
        R.restriction_2_5 L L (Set.Subset.refl _)⟩,?_⟩
      simp
  | @insert e s hes ih =>
      obtain ⟨S,hS⟩ := ih (fun r hr => hpositive r (Finset.mem_insert_of_mem hr))
        (fun r hr => hars r (Finset.mem_insert_of_mem hr))
      by_cases he : cardTable M e = 0
      · refine ⟨S,?_⟩
        intro r hr hn
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact False.elim (hn he)
        · exact hS r hr hn
      · obtain ⟨T,hT⟩ := contraction_factors_stage G F R S.language S.preprocessed
          (S.not_oneSided htwo) S.even S.divisible M (realizable_mono S.contains hM) e
          (hpositive e (Finset.mem_insert_self _ _)) he
          (hars e (Finset.mem_insert_self _ _) he)
        refine ⟨S.trans T,?_⟩
        intro r hr hn
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact hT
        · obtain ⟨W⟩ := hS r hr hn
          exact ⟨W.mono T.contains⟩

end Paper2.SourceFaithful.HighHeight
