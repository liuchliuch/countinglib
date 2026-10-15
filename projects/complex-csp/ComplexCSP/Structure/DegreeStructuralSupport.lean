import ComplexCSP.Recognition.DegreeGenerated
import ComplexCSP.Structure.SupportMaltsevBridge

/-! # Degree-divisible equality-free support closure

Every closure step below carries an actual degree-divisible presentation.
The resulting Mal'tsev theorem uses only rectangularity within this restricted
family, never rectangularity of all ordinary generated tables.
-/
namespace ComplexCSP
open scoped BigOperators
open MaltsevRelations

namespace DegreeGenerated
variable {D K ι B H : Type} [Fintype D] [CommSemiring K]
    {L : Language D K ι} [DecidableEq B] {δ : ℕ}

/-- Canonically encode the hidden variables of an actual degree-certified instance. -/
theorem partition [Fintype H] [DecidableEq H] (I : Instance L B H)
    (hI : I.DegreeDivisible δ) : DegreeGenerated L δ I.partition := by
  classical
  refine ⟨⟨Fintype.card H, I.renameHidden (Fintype.equivFin H)⟩,
    (Instance.degreeDivisible_renameHidden_equiv_iff I (Fintype.equivFin H) δ).mpr hI, ?_⟩
  funext a
  exact Instance.partition_renameHidden_equiv I (Fintype.equivFin H) a

/-- Finite hidden-block marginalization retains every degree certificate. -/
theorem marginal_finite [Fintype B] [Fintype H] [DecidableEq H]
    {G : (B ⊕ H → D) → K} (hG : DegreeGenerated L δ G) :
    DegreeGenerated L δ (fun a => ∑ b : H → D, G (Sum.elim a b)) := by
  obtain ⟨P, hP, rfl⟩ := hG
  have h := partition P.inst.hideBoundary hP.hideBoundary
  have he : P.inst.hideBoundary.partition = (fun a => ∑ b : H → D, P.table (Sum.elim a b)) := by
    funext a
    exact Instance.partition_hideBoundary P.inst a
  rwa [he] at h

/-- A literal finite product uses repeated degree-preserving gluing. -/
theorem finset_prod [Fintype B] {A : Type} (s : Finset A)
    (G : A → (B → D) → K) (hG : ∀ i ∈ s, DegreeGenerated L δ (G i)) :
    DegreeGenerated L δ (fun a => ∏ i ∈ s, G i a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one (B := B) (L := L) δ)
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using
      mul (hG i (Finset.mem_insert_self i s))
        (ih (fun j hj => hG j (Finset.mem_insert_of_mem hj)))

end DegreeGenerated

namespace DegreeGenerated
variable {D K ι B H : Type} [Fintype D] [CommRing K] [IsDomain K]
    {L : Language D K ι} [Fintype B] [DecidableEq B] {δ : ℕ}

/-- Literal finite conjunction with arbitrary scopes, including repeated variables. -/
theorem conjunction_support {A : Type} [Fintype A] (arity : A → ℕ)
    (G : (i : A) → (Fin (arity i) → D) → K)
    (hG : ∀ i, DegreeGenerated L δ (G i)) (scope : (i : A) → Fin (arity i) → B) :
    ∃ F : (B → D) → K, DegreeGenerated L δ F ∧
      ∀ a, F a ≠ 0 ↔ ∀ i, G i (a ∘ scope i) ≠ 0 := by
  classical
  refine ⟨fun a => ∏ i, G i (a ∘ scope i), ?_, ?_⟩
  · apply finset_prod Finset.univ
    intro i _
    exact (hG i).diagonal_minor (scope i)
  · intro a
    simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left]

/-- Power amplification controls cancellation while preserving divisibility. -/
theorem existential_support [Fintype H] [DecidableEq H] [CharZero K]
    {G : (B ⊕ H → D) → K} (hG : DegreeGenerated L δ G) :
    ∃ F : (B → D) → K, DegreeGenerated L δ F ∧
      ∀ a, F a ≠ 0 ↔ ∃ b : H → D, G (Sum.elim a b) ≠ 0 := by
  obtain ⟨m, _, hs⟩ := exists_power_preserving_existential_support
    (fun (a : B → D) (b : H → D) => G (Sum.elim a b))
  exact ⟨fun a => ∑ b : H → D, G (Sum.elim a b) ^ m,
    (hG.pow m).marginal_finite, hs⟩

/-- Genuine degree-restricted equality-free pp closure. -/
theorem equalityfree_pp_support [Fintype H] [DecidableEq H] [CharZero K]
    {A : Type} [Fintype A] (arity : A → ℕ)
    (G : (i : A) → (Fin (arity i) → D) → K)
    (hG : ∀ i, DegreeGenerated L δ (G i)) (scope : (i : A) → Fin (arity i) → B ⊕ H) :
    ∃ F : (B → D) → K, DegreeGenerated L δ F ∧
      ∀ a, F a ≠ 0 ↔ ∃ b : H → D, ∀ i, G i (Sum.elim a b ∘ scope i) ≠ 0 := by
  obtain ⟨P, hP, hPs⟩ := conjunction_support arity G hG scope
  obtain ⟨F, hF, hFs⟩ := existential_support hP
  exact ⟨F, hF, fun a => by simp only [hFs, hPs]⟩
end DegreeGenerated

variable {D K ι : Type} {L : Language D K ι}

/-- Supports with actual degree-divisible finite presentation witnesses. -/
def degreeGeneratedSupports [CommSemiring K] [Fintype D] (L : Language D K ι) (δ : ℕ) :
    Set (Relation D) :=
  {R | ∃ G : (Fin R.arity → D) → K, DegreeGenerated L δ G ∧ R.tuples = {a | G a ≠ 0}}

/-- Three-corner rectangularity only inside the degree-generated family. -/
def AllDegreeGeneratedSupportRectangular [CommSemiring K] [Fintype D]
    (L : Language D K ι) (δ : ℕ) : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B]
    (G : (B ⊕ Unit → D) → K), DegreeGenerated L δ G →
      Rectangular (fun a z => G (Sum.elim a (fun _ => z)) ≠ 0)

/-- The true generated-support pp closure supplies every relational projection
required by the finite repair construction. -/
theorem degree_generated_supports_equalityfree_rectangularity
    [Fintype D] [CommRing K] [IsDomain K] [CharZero K]
    {δ : ℕ} (hrect : AllDegreeGeneratedSupportRectangular L δ) :
    EqualityFreeSingletonRectangularity (degreeGeneratedSupports L δ) := by
  classical
  intro V A _ _ C hC s c hc x y a b hxa hya hxb
  have hG : ∀ i, ∃ G : (Fin (C.relation i).arity → D) → K,
      DegreeGenerated L δ G ∧ (C.relation i).tuples = {w | G w ≠ 0} := hC
  choose G hGen hSupp using hG
  obtain ⟨P, hP, hPs⟩ := DegreeGenerated.conjunction_support
    (fun i => (C.relation i).arity) G hGen C.scope
  have hp (p : V → D) : P p ≠ 0 ↔ C.Satisfies p := by
    rw [hPs]
    simp only [EqualityFreeConjunction.Satisfies, hSupp, Set.mem_ofPred_eq, Function.comp_def]
  have hpull := DegreeGenerated.diagonal_minor hP (projectionScope s c)
  obtain ⟨F, hF, hFs⟩ := DegreeGenerated.existential_support hpull
  have hsupport (r : V → D) (z : D) :
      F (Sum.elim (fun v : s => r v) (fun _ => z)) ≠ 0 ↔
      ProjectLast {p | C.Satisfies p} s c r z := by
    rw [hFs]
    constructor
    · rintro ⟨w, hw⟩
      refine ⟨projectionAssignment s c (fun v => r v) z w, (hp _).mp hw, ?_, ?_⟩
      · intro v hv
        exact projectionAssignment_row s c (fun v => r v) z w ⟨v, hv⟩
      · exact projectionAssignment_last s c hc _ _ _
    · rintro ⟨p, hsat, hrow, hlast⟩
      refine ⟨fun v => p v, ?_⟩
      apply (hp _).mpr
      have he : projectionAssignment s c (fun v : s => r v) z (fun v => p v) = p := by
        calc
          _ = projectionAssignment s c (fun v => p v) (p c) (fun v => p v) := by
            congr 1
            · funext v
              exact (hrow v v.property).symm
            · exact hlast.symm
          _ = p := projectionAssignment_recover s c p
      change C.Satisfies (projectionAssignment s c _ z _)
      rw [he]
      exact hsat
  apply (hsupport y b).mp
  exact hrect s F hF (fun v => x v) (fun v => y v) a b
    ((hsupport x a).mpr hxa) ((hsupport y a).mpr hya) ((hsupport x b).mpr hxb)

/-- The entire common-operation construction is now connected to actual generated
supports. The sole remaining premise is the displayed generated-support
rectangularity, which is supplied later from legal global purification. -/
theorem common_maltsev_of_degree_generated_support_rectangularity
    [Fintype D] [Nonempty D] [CommRing K] [IsDomain K] [CharZero K]
    {δ : ℕ} (hrect : AllDegreeGeneratedSupportRectangular L δ) :
    ∃ m : Operation D, IsMaltsev m ∧ CommonPolymorphism (degreeGeneratedSupports L δ) m :=
  common_maltsev_of_equalityfree_rectangularity (degreeGeneratedSupports L δ)
    (degree_generated_supports_equalityfree_rectangularity hrect)

end ComplexCSP
