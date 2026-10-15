import ComplexCSP.Recognition.DegreeFilter
import ComplexCSP.Instances.PinnedMonoid
import Mathlib.Data.List.Count

/-!
# Actual degree-divisible generated families

All degree restrictions are properties of actual finite presentation witnesses.
Boundary identification, hidden relabeling, gluing, marginalization, and powers
preserve divisibility by counting every scope position with its multiplicity.
-/

set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP

open scoped BigOperators

/-- Count the preimages of a value under an arbitrary map of an occurrence list.
The map need not be injective, so repeated/identified variables are retained. -/
theorem list_count_map_fiber {V W : Type} [Fintype V] [DecidableEq V] [DecidableEq W]
    (l : List V) (f : V → W) (w : W) :
    (l.map f).count w = ∑ v, if f v = w then l.count v else 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have hv (v : V) : (if f v = w then (a :: l).count v else 0) =
        (if v = a then (if f a = w then 1 else 0) else 0) +
          (if f v = w then l.count v else 0) := by
      by_cases hva : v = a
      · subst v
        by_cases hfw : f a = w <;> simp [hfw, Nat.add_comm]
      · by_cases hfw : f v = w <;> simp [hva, Ne.symm hva, hfw]
    simp only [List.map_cons, hv, Finset.sum_add_distrib]
    simp [ih, List.count_cons, Nat.add_comm]

namespace Instance

variable {D K ι B C H J : Type} {L : Language D K ι}

/-- Map all variables while keeping every constraint and scope position. -/
def mapVariables (I : Instance L B H) (f : B ⊕ H → C ⊕ J) : Instance L C J :=
  ⟨I.constraints.map (fun c => c.rename f)⟩

/-- The occurrence list transforms by the literal map, without deduplication. -/
theorem occurrences_mapVariables (I : Instance L B H) (f : B ⊕ H → C ⊕ J) :
    (I.mapVariables f).occurrences = I.occurrences.map f := by
  cases I with
  | mk cs =>
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [mapVariables, occurrences, List.map_cons, List.flatMap_cons,
        List.map_append, List.map_ofFn, Constraint.rename, Function.comp_def] at ih ⊢
      rw [ih]

/-- Every target degree is the sum of all source degrees in its preimage. -/
theorem occurrenceDegree_mapVariables [Fintype B] [Fintype H]
    [DecidableEq B] [DecidableEq H] [DecidableEq C] [DecidableEq J]
    (I : Instance L B H) (f : B ⊕ H → C ⊕ J) (w : C ⊕ J) :
    (I.mapVariables f).occurrenceDegree w =
      ∑ v, if f v = w then I.occurrenceDegree v else 0 := by
  unfold occurrenceDegree
  rw [occurrences_mapVariables]
  exact list_count_map_fiber I.occurrences f w

/-- Boundary identification adds the occurrence degrees of all identified labels.
The displayed formula also treats hidden variables, which are unchanged. -/
theorem occurrenceDegree_renameBoundary [Fintype B] [Fintype H]
    [DecidableEq B] [DecidableEq H] [DecidableEq C]
    (I : Instance L B H) (f : B → C) (w : C ⊕ H) :
    (I.renameBoundary f).occurrenceDegree w =
      ∑ v, if Sum.map f id v = w then I.occurrenceDegree v else 0 :=
  occurrenceDegree_mapVariables I (Sum.map f id) w

/-- A more familiar form of the boundary-preimage degree formula. -/
theorem boundary_degree_renameBoundary [Fintype B] [Fintype H]
    [DecidableEq B] [DecidableEq H] [DecidableEq C]
    (I : Instance L B H) (f : B → C) (w : C) :
    (I.renameBoundary f).occurrenceDegree (Sum.inl w) =
      ∑ v : B, if f v = w then I.occurrenceDegree (Sum.inl v) else 0 := by
  rw [occurrenceDegree_renameBoundary]
  simp [Fintype.sum_sum_type]

/-- A hidden-variable bijection preserves each corresponding degree exactly. -/
theorem occurrenceDegree_renameHidden_equiv
    [DecidableEq B] [DecidableEq H] [DecidableEq J]
    (I : Instance L B H) (e : H ≃ J) (v : B ⊕ H) :
    (I.renameHidden e).occurrenceDegree (Sum.map id e v) = I.occurrenceDegree v := by
  change (I.mapVariables (Sum.map id e)).occurrenceDegree (Sum.map id e v) = _
  unfold occurrenceDegree
  rw [occurrences_mapVariables]
  exact @List.count_map_of_injective (B ⊕ H) (B ⊕ J)
    (instBEqOfDecidableEq) (instLawfulBEq) (instBEqOfDecidableEq) (instLawfulBEq)
    I.occurrences (Sum.map id e)
    (Equiv.sumCongr (Equiv.refl B) e).injective v

/-- Degree-divisible is a property of an actual instance, not just its table. -/
def DegreeDivisible [DecidableEq B] [DecidableEq H] (δ : ℕ) (I : Instance L B H) : Prop :=
  ∀ v, δ ∣ I.occurrenceDegree v

/-- Degree divisibility of a finite literal instance is decidable by counting
its explicitly supplied occurrence lists. No classical decision is installed. -/
instance decidableDegreeDivisible [Fintype B] [Fintype H]
    [DecidableEq B] [DecidableEq H] (δ : ℕ) (I : Instance L B H) :
    Decidable (I.DegreeDivisible δ) :=
  inferInstanceAs (Decidable (∀ v, δ ∣ I.occurrenceDegree v))

/-- Arbitrary variable identifications preserve divisibility, since target
degrees are sums of source degrees. -/
theorem DegreeDivisible.mapVariables [Fintype B] [Fintype H]
    [DecidableEq B] [DecidableEq H] [DecidableEq C] [DecidableEq J]
    {δ : ℕ} {I : Instance L B H} (hI : I.DegreeDivisible δ)
    (f : B ⊕ H → C ⊕ J) : (I.mapVariables f).DegreeDivisible δ := by
  intro w
  rw [occurrenceDegree_mapVariables]
  apply Finset.dvd_sum
  intro v hv
  split_ifs
  · exact hI v
  · exact dvd_zero δ

/-- In particular, actual external diagonal-minor construction preserves degrees. -/
theorem DegreeDivisible.renameBoundary [Fintype B] [Fintype H]
    [DecidableEq B] [DecidableEq H] [DecidableEq C]
    {δ : ℕ} {I : Instance L B H} (hI : I.DegreeDivisible δ) (f : B → C) :
    (I.renameBoundary f).DegreeDivisible δ := hI.mapVariables (Sum.map f id)

/-- Hidden-variable bijections preserve divisibility in both directions. -/
theorem degreeDivisible_renameHidden_equiv_iff
    [DecidableEq B] [DecidableEq H] [DecidableEq J]
    (I : Instance L B H) (e : H ≃ J) (δ : ℕ) :
    (I.renameHidden e).DegreeDivisible δ ↔ I.DegreeDivisible δ := by
  constructor
  · intro h v
    simpa only [occurrenceDegree_renameHidden_equiv] using h (Sum.map id e v)
  · intro h w
    obtain ⟨v, rfl⟩ := (Equiv.sumCongr (Equiv.refl B) e).surjective w
    change δ ∣ (I.renameHidden e).occurrenceDegree (Sum.map id e v)
    rw [occurrenceDegree_renameHidden_equiv]
    exact h v

/-- The occurrence list of a glued instance is the concatenation of its two
renamed occurrence lists; hidden copies remain disjoint. -/
theorem occurrences_glue {H₁ H₂ : Type} (I : Instance L B H₁) (J : Instance L B H₂) :
    (I.glue J).occurrences =
      (I.renameHidden Sum.inl).occurrences ++ (J.renameHidden Sum.inr).occurrences := by
  simp only [occurrences, glue, List.flatMap_append]

/-- Occurrence degrees add under literal constraint-list gluing. -/
theorem occurrenceDegree_glue {H₁ H₂ : Type}
    [DecidableEq B] [DecidableEq H₁] [DecidableEq H₂]
    (I : Instance L B H₁) (J : Instance L B H₂) (v : B ⊕ (H₁ ⊕ H₂)) :
    (I.glue J).occurrenceDegree v =
      (I.renameHidden Sum.inl).occurrenceDegree v +
        (J.renameHidden Sum.inr).occurrenceDegree v := by
  simp only [occurrenceDegree, occurrences_glue, List.count_append]

/-- Actual gluing preserves degree divisibility. -/
theorem DegreeDivisible.glue {H₁ H₂ : Type} [Fintype B] [Fintype H₁] [Fintype H₂]
    [DecidableEq B] [DecidableEq H₁] [DecidableEq H₂]
    {δ : ℕ} {I : Instance L B H₁} {J : Instance L B H₂}
    (hI : I.DegreeDivisible δ) (hJ : J.DegreeDivisible δ) :
    (I.glue J).DegreeDivisible δ := by
  intro v
  rw [occurrenceDegree_glue]
  exact dvd_add (hI.mapVariables (Sum.map id Sum.inl) v)
    (hJ.mapVariables (Sum.map id Sum.inr) v)

/-- Marginalization keeps the degree of every corresponding variable unchanged. -/
theorem occurrenceDegree_hideBoundary {H₁ H₂ : Type}
    [DecidableEq B] [DecidableEq H₁] [DecidableEq H₂]
    (I : Instance L (B ⊕ H₁) H₂) (v : (B ⊕ H₁) ⊕ H₂) :
    I.hideBoundary.occurrenceDegree ((Equiv.sumAssoc B H₁ H₂) v) =
      I.occurrenceDegree v := by
  change (I.mapVariables (Equiv.sumAssoc B H₁ H₂)).occurrenceDegree
    ((Equiv.sumAssoc B H₁ H₂) v) = _
  unfold occurrenceDegree
  rw [occurrences_mapVariables]
  exact @List.count_map_of_injective ((B ⊕ H₁) ⊕ H₂) (B ⊕ (H₁ ⊕ H₂))
    (instBEqOfDecidableEq) (instLawfulBEq) (instBEqOfDecidableEq) (instLawfulBEq)
    I.occurrences (Equiv.sumAssoc B H₁ H₂)
    (Equiv.sumAssoc B H₁ H₂).injective v

/-- Moving retained variables into the hidden block only relabels variables. -/
theorem DegreeDivisible.hideBoundary {H₁ H₂ : Type}
    [Fintype B] [Fintype H₁] [Fintype H₂]
    [DecidableEq B] [DecidableEq H₁] [DecidableEq H₂]
    {δ : ℕ} {I : Instance L (B ⊕ H₁) H₂} (hI : I.DegreeDivisible δ) :
    I.hideBoundary.DegreeDivisible δ :=
  hI.mapVariables (Equiv.sumAssoc B H₁ H₂)

end Instance

namespace Presentation

variable {D K ι B C : Type} {L : Language D K ι}

/-- Every actual variable in the presentation has occurrence degree divisible by δ. -/
def DegreeDivisible [DecidableEq B] (δ : ℕ) (P : Presentation L B) : Prop :=
  P.inst.DegreeDivisible δ

/-- Executable membership check for the degree restriction on presentations. -/
instance decidableDegreeDivisible [Fintype B] [DecidableEq B]
    (δ : ℕ) (P : Presentation L B) : Decidable (P.DegreeDivisible δ) :=
  inferInstanceAs (Decidable (P.inst.DegreeDivisible δ))

/-- A finite Boolean degree check using actual scope-position counts. -/
def degreeDivisibilityTest [Fintype B] [DecidableEq B]
    (δ : ℕ) (P : Presentation L B) : Bool := decide (P.DegreeDivisible δ)

@[simp] theorem degreeDivisibilityTest_correct [Fintype B] [DecidableEq B]
    (δ : ℕ) (P : Presentation L B) :
    P.degreeDivisibilityTest δ = true ↔ P.DegreeDivisible δ := by
  simp [degreeDivisibilityTest]

/-- The unit presentation has degree zero at every boundary variable. -/
theorem degreeDivisible_one [DecidableEq B] (δ : ℕ) :
    (one : Presentation L B).DegreeDivisible δ := by
  intro v
  simp [one, Instance.occurrenceDegree, Instance.occurrences]

/-- Boundary identification on the executable presentation preserves divisibility. -/
theorem DegreeDivisible.rename [Fintype B] [DecidableEq B] [DecidableEq C]
    {δ : ℕ} {P : Presentation L B} (hP : P.DegreeDivisible δ) (f : B → C) :
    (P.rename f).DegreeDivisible δ := hP.renameBoundary f

/-- The finite canonical hidden-index encoding does not affect divisibility. -/
theorem DegreeDivisible.mul [Fintype B] [DecidableEq B]
    {δ : ℕ} {P Q : Presentation L B} (hP : P.DegreeDivisible δ)
    (hQ : Q.DegreeDivisible δ) : (P.mul Q).DegreeDivisible δ := by
  exact (Instance.degreeDivisible_renameHidden_equiv_iff
    (P.inst.glue Q.inst) finSumFinEquiv δ).mpr (hP.glue hQ)

/-- Every actual independent-copy power preserves the degree restriction. -/
theorem DegreeDivisible.power [Fintype B] [DecidableEq B]
    {δ : ℕ} {P : Presentation L B} (hP : P.DegreeDivisible δ) (n : ℕ) :
    (P.power n).DegreeDivisible δ := by
  induction n with
  | zero => exact degreeDivisible_one δ
  | succ n ih => exact ih.mul hP

/-- A finite product of degree-divisible presentations is degree-divisible. -/
theorem degreeDivisible_product [Fintype B] [DecidableEq B]
    {δ : ℕ} (Ps : List (Presentation L B))
    (hPs : ∀ P ∈ Ps, P.DegreeDivisible δ) : (product Ps).DegreeDivisible δ := by
  induction Ps with
  | nil => exact degreeDivisible_one δ
  | cons P Ps ih =>
    exact (hPs P (List.mem_cons_self)).mul
      (ih (fun Q hQ => hPs Q (List.mem_cons_of_mem P hQ)))

/-- The actual finite marginalization compiler preserves degree divisibility. -/
theorem DegreeDivisible.marginal [Fintype B] [DecidableEq B]
    {δ h : ℕ} {P : Presentation L (B ⊕ Fin h)} (hP : P.DegreeDivisible δ) :
    P.marginal.DegreeDivisible δ := by
  exact (Instance.degreeDivisible_renameHidden_equiv_iff
    P.inst.hideBoundary finSumFinEquiv δ).mpr hP.hideBoundary

/-- The exact power-search support compiler stays inside the degree-restricted
family, because both its amplification and its marginalization do. -/
theorem DegreeDivisible.existentialSupport [Fintype D] [Fintype B] [DecidableEq B]
    [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K]
    {δ h : ℕ} {P : Presentation L (B ⊕ Fin h)} (hP : P.DegreeDivisible δ) :
    P.existentialSupport.DegreeDivisible δ :=
  (hP.power _).marginal

end Presentation

namespace PresentedAtom

variable {D K ι B V : Type} {L : Language D K ι}

/-- Literal equality-free atoms retain divisibility after scope identification. -/
theorem degreeDivisible_lift [DecidableEq V] {δ : ℕ} (A : PresentedAtom L V)
    (hA : A.presentation.DegreeDivisible δ) : A.lift.DegreeDivisible δ :=
  hA.rename A.scope

/-- The full executable equality-free pp compiler preserves the degree restriction. -/
theorem degreeDivisible_compile [Fintype D] [Fintype B] [DecidableEq B]
    [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K]
    {δ h : ℕ} (atoms : List (PresentedAtom L (B ⊕ Fin h)))
    (hatoms : ∀ A ∈ atoms, A.presentation.DegreeDivisible δ) :
    (compile atoms).DegreeDivisible δ := by
  apply Presentation.DegreeDivisible.existentialSupport
  apply Presentation.degreeDivisible_product
  intro P hP
  obtain ⟨A, hA, rfl⟩ := List.mem_map.mp hP
  exact degreeDivisible_lift A (hatoms A hA)

end PresentedAtom

section DegreeGenerated

variable {D K ι B C : Type} [CommSemiring K] [Fintype D]
variable {L : Language D K ι}

/-- A table is degree-generated when an actual degree-divisible presentation
witnesses it. This definition does not assign a degree to the table itself. -/
def DegreeGenerated [DecidableEq B] (L : Language D K ι) (δ : ℕ)
    (G : (B → D) → K) : Prop :=
  ∃ P : Presentation L B, P.DegreeDivisible δ ∧ P.table = G

namespace DegreeGenerated

variable [DecidableEq B]

/-- Forgetting the degree certificate leaves an ordinary generated-table witness. -/
theorem generated {δ : ℕ} {G : (B → D) → K} (hG : DegreeGenerated L δ G) :
    Instance.Generated L G := by
  obtain ⟨P, hP, rfl⟩ := hG
  exact P.table_generated

/-- The size-one degree restriction is exactly the ordinary generated family. -/
theorem at_one_iff {G : (B → D) → K} :
    DegreeGenerated L 1 G ↔ Instance.Generated L G := by
  constructor
  · exact generated
  · rintro ⟨n, I, hI⟩
    exact ⟨⟨n, I⟩, (fun v => one_dvd (I.occurrenceDegree v)), funext hI⟩

/-- The constant-one table has an actual degree-zero witness. -/
theorem one (δ : ℕ) : DegreeGenerated L δ (fun _ : B → D => 1) := by
  refine ⟨Presentation.one, Presentation.degreeDivisible_one δ, ?_⟩
  funext a
  exact Presentation.table_one (L := L) a

/-- Actual disjoint-copy gluing proves multiplication closure. -/
theorem mul [Fintype B] {δ : ℕ} {G F : (B → D) → K}
    (hG : DegreeGenerated L δ G) (hF : DegreeGenerated L δ F) :
    DegreeGenerated L δ (fun a => G a * F a) := by
  obtain ⟨P, hP, rfl⟩ := hG
  obtain ⟨Q, hQ, rfl⟩ := hF
  refine ⟨P.mul Q, hP.mul hQ, ?_⟩
  funext a
  exact Presentation.table_mul P Q a

/-- Every independent-copy power has a degree-divisible witness. -/
theorem pow [Fintype B] {δ : ℕ} {G : (B → D) → K}
    (hG : DegreeGenerated L δ G) (n : ℕ) :
    DegreeGenerated L δ (fun a => G a ^ n) := by
  obtain ⟨P, hP, rfl⟩ := hG
  refine ⟨P.power n, hP.power n, ?_⟩
  funext a
  exact Presentation.table_power P n a

/-- Degree-generated tables are closed under all boundary identifications. -/
theorem diagonal_minor [Fintype B] [DecidableEq C] {δ : ℕ} {G : (B → D) → K}
    (hG : DegreeGenerated L δ G) (f : B → C) :
    DegreeGenerated L δ (fun a => G (a ∘ f)) := by
  obtain ⟨P, hP, rfl⟩ := hG
  refine ⟨P.rename f, hP.rename f, ?_⟩
  funext a
  exact Presentation.table_rename P f a

/-- Summing a finite retained block preserves the degree-generated family. -/
theorem marginal [Fintype B] {δ h : ℕ} {G : (B ⊕ Fin h → D) → K}
    (hG : DegreeGenerated L δ G) :
    DegreeGenerated L δ (fun a => ∑ b : Fin h → D, G (Sum.elim a b)) := by
  obtain ⟨P, hP, rfl⟩ := hG
  refine ⟨P.marginal, hP.marginal, ?_⟩
  funext a
  exact Presentation.table_marginal P a

end DegreeGenerated

/-- A genuine semantic submonoid whose membership retains an existential
actual degree-divisible presentation witness. -/
def degreeGeneratedTableSubmonoid [Fintype B] [DecidableEq B]
    (L : Language D K ι) (δ : ℕ) : Submonoid ((B → D) → K) where
  carrier := {G | DegreeGenerated L δ G}
  one_mem' := DegreeGenerated.one δ
  mul_mem' := fun hG hF => DegreeGenerated.mul hG hF

abbrev DegreeGeneratedTable [Fintype B] [DecidableEq B] (L : Language D K ι) (δ : ℕ) :=
  degreeGeneratedTableSubmonoid (B := B) L δ

namespace DegreeGeneratedTable

variable [Fintype B] [DecidableEq B] {δ : ℕ}

/-- Interpret a certified actual presentation in the degree-generated monoid. -/
def ofPresentation (P : Presentation L B) (hP : P.DegreeDivisible δ) :
    DegreeGeneratedTable (B := B) L δ := ⟨P.table, P, hP, rfl⟩

/-- Every semantic element retains an actual degree-certified presentation. -/
theorem exists_presentation (G : DegreeGeneratedTable (B := B) L δ) :
    ∃ P : Presentation L B, ∃ hP : P.DegreeDivisible δ, ofPresentation P hP = G := by
  obtain ⟨P, hP, he⟩ := G.property
  exact ⟨P, hP, Subtype.ext he⟩

/-- Forgetting the degree certificate is a monoid homomorphism into the ordinary
generated-table monoid. -/
def inclusion : DegreeGeneratedTable (B := B) L δ →* GeneratedTable L B where
  toFun G := ⟨G.val, G.property.generated⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Universal assertions are precisely assertions on all degree-certified
finite presentations, rather than an enlarged abstract family. -/
theorem forall_iff_presentations (Q : ((B → D) → K) → Prop) :
    (∀ G : DegreeGeneratedTable (B := B) L δ, Q G.val) ↔
      ∀ P : Presentation L B, P.DegreeDivisible δ → Q P.table := by
  constructor
  · intro h P hP
    exact h (ofPresentation P hP)
  · intro h G
    obtain ⟨P, hP, rfl⟩ := exists_presentation G
    exact h P hP

omit [Fintype B] in
/-- An exact reformulation over literal canonical finite hidden-variable instances. -/
theorem forall_presentations_iff_instances (Q : ((B → D) → K) → Prop) :
    (∀ P : Presentation L B, P.DegreeDivisible δ → Q P.table) ↔
      ∀ n : ℕ, ∀ I : Instance L B (Fin n), I.DegreeDivisible δ → Q I.partition := by
  constructor
  · intro h n I hI
    exact h ⟨n, I⟩ hI
  · rintro h ⟨n, I⟩ hI
    exact h n I hI

end DegreeGeneratedTable

end DegreeGenerated

section RestrictedCharacters

variable {D K ι B : Type} [CommSemiring K] [Fintype D] [Fintype B] [DecidableEq B]

/-- A genuine pinned character on the degree-generated monoid. -/
def degreePinnedCharacter (L : Language D K ι) (δ : ℕ) (a : B → D) :
    DegreeGeneratedTable (B := B) L δ →* K :=
  (pinnedCharacter L a).comp DegreeGeneratedTable.inclusion

@[simp] theorem degreePinnedCharacter_apply (L : Language D K ι) (δ : ℕ)
    (a : B → D) (G : DegreeGeneratedTable (B := B) L δ) :
    degreePinnedCharacter L δ a G = G.val a := rfl

variable [StarRing K]

/-- Restrict a direct/conjugate monomial character to the actual degree-generated
family. The inclusion is a proved monoid homomorphism. -/
def degreePinnedExponentCharacter (L : Language D K ι) (δ : ℕ)
    (d : PinnedCoordinate B D →₀ ℕ) : DegreeGeneratedTable (B := B) L δ →* K :=
  (pinnedExponentCharacter L d).comp DegreeGeneratedTable.inclusion

@[simp] theorem degreePinnedExponentCharacter_apply (L : Language D K ι) (δ : ℕ)
    (d : PinnedCoordinate B D →₀ ℕ) (G : DegreeGeneratedTable (B := B) L δ) :
    degreePinnedExponentCharacter L δ d G =
      ∏ v ∈ d.support, (Sum.elim G.val (fun a => star (G.val a)) v) ^ d v :=
  pinnedExponentCharacter_apply L d (DegreeGeneratedTable.inclusion G)

/-- The actual formal polynomial expansion is valid on the restricted monoid. -/
theorem degree_polynomial_eval_as_characters (L : Language D K ι) (δ : ℕ)
    (p : MvPolynomial (PinnedCoordinate B D) K)
    (G : DegreeGeneratedTable (B := B) L δ) :
    MvPolynomial.eval (Sum.elim G.val (fun a => star (G.val a))) p =
      ∑ d ∈ p.support, p.coeff d * degreePinnedExponentCharacter L δ d G := by
  have h := polynomial_eval_as_characters L p (DegreeGeneratedTable.inclusion G)
  simp only [degreePinnedExponentCharacter, MonoidHom.comp_apply]
  exact h

/-- Universal polynomial identities on the restricted monoid are exactly
universal identities on the actual degree-divisible presentations. -/
theorem degree_polynomial_identity_iff_presentations (L : Language D K ι) (δ : ℕ)
    (p : MvPolynomial (PinnedCoordinate B D) K) :
    (∀ G : DegreeGeneratedTable (B := B) L δ,
      MvPolynomial.eval (Sum.elim G.val (fun a => star (G.val a))) p = 0) ↔
      ∀ P : Presentation L B, P.DegreeDivisible δ →
        MvPolynomial.eval (Sum.elim P.table (fun a => star (P.table a))) p = 0 :=
  DegreeGeneratedTable.forall_iff_presentations
    (fun G => MvPolynomial.eval (Sum.elim G (fun a => star (G a))) p = 0)

end RestrictedCharacters

section RestrictedIdentityTest

variable {D K ι B : Type} [Field K] [StarRing K] [DecidableEq K]
variable [Fintype D] [Fintype B] [DecidableEq B]

/-- The finite grouping test is sound and complete for degree-multiple generated
polynomial identities, relative only to a verified finite comparison matrix.
This is not an implementation of character comparison or an additional oracle axiom. -/
theorem degree_polynomial_identity_test_correct (L : Language D K ι) (δ : ℕ)
    (p : MvPolynomial (PinnedCoordinate B D) K)
    (same : (PinnedCoordinate B D →₀ ℕ) → (PinnedCoordinate B D →₀ ℕ) → Bool)
    (hsame : ∀ d ∈ p.support, ∀ e ∈ p.support,
      same d e = true ↔
        degreePinnedExponentCharacter L δ d = degreePinnedExponentCharacter L δ e) :
    indexedCharacterZeroTest p.support same p.coeff = true ↔
      ∀ P : Presentation L B, P.DegreeDivisible δ →
        MvPolynomial.eval (Sum.elim P.table (fun a => star (P.table a))) p = 0 := by
  rw [indexedCharacterZeroTest_correct p.support (degreePinnedExponentCharacter L δ)
    same p.coeff hsame]
  simp_rw [← degree_polynomial_eval_as_characters]
  exact degree_polynomial_identity_iff_presentations L δ p

/-- Rejection yields an actual finite degree-divisible counterexample presentation. -/
theorem degree_polynomial_identity_test_rejects_iff (L : Language D K ι) (δ : ℕ)
    (p : MvPolynomial (PinnedCoordinate B D) K)
    (same : (PinnedCoordinate B D →₀ ℕ) → (PinnedCoordinate B D →₀ ℕ) → Bool)
    (hsame : ∀ d ∈ p.support, ∀ e ∈ p.support,
      same d e = true ↔
        degreePinnedExponentCharacter L δ d = degreePinnedExponentCharacter L δ e) :
    indexedCharacterZeroTest p.support same p.coeff = false ↔
      ∃ P : Presentation L B, P.DegreeDivisible δ ∧
        MvPolynomial.eval (Sum.elim P.table (fun a => star (P.table a))) p ≠ 0 := by
  classical
  rw [← Bool.not_eq_true, degree_polynomial_identity_test_correct L δ p same hsame]
  push_neg
  rfl

end RestrictedIdentityTest

end ComplexCSP
