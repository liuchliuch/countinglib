import ComplexCSP.Structure.SupportRealization
import ComplexCSP.Structure.MaltsevRelations

/-! # From actual generated-support rectangularity to one Mal'tsev operation

This bridges the proved finite-instance pp construction to the relational repair
argument. Rectangularity is an explicit three-corner property of generated tables;
no common operation or pp-closure result is assumed.
-/
namespace ComplexCSP
open MaltsevRelations

variable {D K ι : Type} {L : Language D K ι}

/-- The supports of the actual generated tables, retaining each numerical arity. -/
def generatedSupports [CommSemiring K] [Fintype D] (L : Language D K ι) :
    Set (Relation D) :=
  {R | ∃ G : (Fin R.arity → D) → K, Instance.Generated L G ∧ R.tuples = {a | G a ≠ 0}}

/-- The singleton-coordinate rectangularity property that the BO support argument
must supply. It quantifies literal generated tables, not assumed pp closures. -/
def AllGeneratedSupportRectangular [CommSemiring K] [Fintype D]
    (L : Language D K ι) : Prop :=
  ∀ (B : Type) [Fintype B] [DecidableEq B]
    (G : (B ⊕ Unit → D) → K), Instance.Generated L G →
      Rectangular (fun a z => G (Sum.elim a (fun _ => z)) ≠ 0)

section Projection
variable {V : Type} [DecidableEq V]

/-- Coordinates outside the retained row cells and the one last cell. -/
abbrev ProjectHidden (s : Finset V) (c : V) := {v : V // v ∉ s ∧ v ≠ c}

/-- A total syntactic renaming of variables into retained and hidden coordinates. -/
def projectionScope (s : Finset V) (c : V) : V → (s ⊕ Unit) ⊕ ProjectHidden s c :=
  fun v => if hs : v ∈ s then Sum.inl (Sum.inl ⟨v, hs⟩)
    else if hc : v = c then Sum.inl (Sum.inr ()) else Sum.inr ⟨v, hs, hc⟩

/-- Reconstitute the assignment on the original variable set. -/
def projectionAssignment (s : Finset V) (c : V) (a : s → D) (z : D)
    (b : ProjectHidden s c → D) : V → D :=
  Sum.elim (Sum.elim a (fun _ => z)) b ∘ projectionScope s c

@[simp] theorem projectionAssignment_row (s : Finset V) (c : V)
    (a : s → D) (z : D) (b : ProjectHidden s c → D) (v : s) :
    projectionAssignment s c a z b v = a v := by simp [projectionAssignment, projectionScope, v.property]

@[simp] theorem projectionAssignment_last (s : Finset V) (c : V) (hc : c ∉ s)
    (a : s → D) (z : D) (b : ProjectHidden s c → D) :
    projectionAssignment s c a z b c = z := by simp [projectionAssignment, projectionScope, hc]

@[simp] theorem projectionAssignment_recover (s : Finset V) (c : V)
    (p : V → D) :
    projectionAssignment s c (fun v => p v) (p c) (fun v => p v) = p := by
  funext v
  unfold projectionAssignment projectionScope
  by_cases hs : v ∈ s
  · simp [hs]
  · by_cases hc : v = c
    · subst v
      simp [hs]
    · simp [hs, hc]

end Projection

/-- The true generated-support pp closure supplies every relational projection
required by the finite repair construction. -/
theorem generated_supports_equalityfree_rectangularity
    [Fintype D] [CommRing K] [IsDomain K] [CharZero K]
    (hrect : AllGeneratedSupportRectangular L) :
    EqualityFreeSingletonRectangularity (generatedSupports L) := by
  classical
  intro V A _ _ C hC s c hc x y a b hxa hya hxb
  have hG : ∀ i, ∃ G : (Fin (C.relation i).arity → D) → K,
      Instance.Generated L G ∧ (C.relation i).tuples = {w | G w ≠ 0} := hC
  choose G hGen hSupp using hG
  obtain ⟨P, hP, hPs⟩ := Instance.generated_conjunction_support
    (fun i => (C.relation i).arity) G hGen C.scope
  have hp (p : V → D) : P p ≠ 0 ↔ C.Satisfies p := by
    rw [hPs]
    simp only [EqualityFreeConjunction.Satisfies, hSupp, Set.mem_ofPred_eq, Function.comp_def]
  have hpull := Instance.generated_diagonal_minor hP (projectionScope s c)
  obtain ⟨F, hF, hFs⟩ := Instance.generated_existential_support hpull
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
theorem common_maltsev_of_generated_support_rectangularity
    [Fintype D] [Nonempty D] [CommRing K] [IsDomain K] [CharZero K]
    (hrect : AllGeneratedSupportRectangular L) :
    ∃ m : Operation D, IsMaltsev m ∧ CommonPolymorphism (generatedSupports L) m :=
  common_maltsev_of_equalityfree_rectangularity (generatedSupports L)
    (generated_supports_equalityfree_rectangularity hrect)

end ComplexCSP
