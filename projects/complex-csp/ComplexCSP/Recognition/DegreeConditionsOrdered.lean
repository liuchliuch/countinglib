import ComplexCSP.Recognition.DegreeGenerated
import ComplexCSP.Instances.OrderedInstances

/-! # Exact ordered semantics of the degree-multiple generated family

The ordered occurrence list counts every scope position and constraint copy.
Splitting retained and hidden coordinates, and flattening them back, preserve
these degrees exactly. Thus degree-generated presentation witnesses are exactly
the paper's ordered degree-divisible partial marginals.
-/
namespace ComplexCSP
variable {D K ι : Type} {L : Language D K ι}

namespace OrderedInstance

/-- Literal scope positions of an ordered instance, with all multiplicities. -/
def occurrences {n : ℕ} (I : OrderedInstance L n) : List (Fin n) :=
  I.constraints.flatMap fun c => List.ofFn c.scope

/-- Exact occurrence degree; isolated variables have degree zero. -/
def occurrenceDegree {n : ℕ} (I : OrderedInstance L n) (v : Fin n) : ℕ :=
  I.occurrences.count v

/-- Every actual ordered variable, including the hidden ones, is restricted. -/
def DegreeDivisible {n : ℕ} (δ : ℕ) (I : OrderedInstance L n) : Prop :=
  ∀ v, δ ∣ I.occurrenceDegree v

variable {r h : ℕ}

theorem occurrences_split (I : OrderedInstance L (r + h)) :
    I.split.occurrences = I.occurrences.map finSumFinEquiv.symm := by
  cases I with
  | mk cs =>
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [split, occurrences, Instance.occurrences, List.map_cons,
        List.flatMap_cons, List.map_append, List.map_ofFn,
        Constraint.rename, Function.comp_def] at ih ⊢
      rw [ih]

/-- Every corresponding ordered degree is unchanged by the boundary split. -/
theorem occurrenceDegree_split (I : OrderedInstance L (r + h)) (v : Fin (r + h)) :
    I.split.occurrenceDegree (finSumFinEquiv.symm v) = I.occurrenceDegree v := by
  unfold Instance.occurrenceDegree occurrenceDegree
  rw [occurrences_split]
  exact @List.count_map_of_injective (Fin (r + h)) (Fin r ⊕ Fin h)
    instBEqOfDecidableEq instLawfulBEq instBEqOfDecidableEq instLawfulBEq
    I.occurrences finSumFinEquiv.symm
    finSumFinEquiv.symm.injective v

theorem degreeDivisible_split_iff (I : OrderedInstance L (r + h)) (δ : ℕ) :
    I.split.DegreeDivisible δ ↔ I.DegreeDivisible δ := by
  constructor
  · intro hI v
    simpa only [occurrenceDegree_split] using hI (finSumFinEquiv.symm v)
  · intro hI w
    obtain ⟨v, rfl⟩ := finSumFinEquiv.symm.surjective w
    rw [occurrenceDegree_split]
    exact hI v
end OrderedInstance

namespace Instance
variable {r h : ℕ}

theorem occurrences_flatten (I : Instance L (Fin r) (Fin h)) :
    I.flatten.occurrences = I.occurrences.map finSumFinEquiv := by
  cases I with
  | mk cs =>
    induction cs with
    | nil => rfl
    | cons c cs ih =>
      simp only [flatten, OrderedInstance.occurrences, occurrences, List.map_cons,
        List.flatMap_cons, List.map_append, List.map_ofFn,
        Constraint.rename, Function.comp_def] at ih ⊢
      rw [ih]

theorem occurrenceDegree_flatten (I : Instance L (Fin r) (Fin h)) (v : Fin r ⊕ Fin h) :
    I.flatten.occurrenceDegree (finSumFinEquiv v) = I.occurrenceDegree v := by
  unfold OrderedInstance.occurrenceDegree occurrenceDegree
  rw [occurrences_flatten]
  exact @List.count_map_of_injective (Fin r ⊕ Fin h) (Fin (r + h))
    instBEqOfDecidableEq instLawfulBEq instBEqOfDecidableEq instLawfulBEq
    I.occurrences finSumFinEquiv
    finSumFinEquiv.injective v

theorem degreeDivisible_flatten_iff (I : Instance L (Fin r) (Fin h)) (δ : ℕ) :
    I.flatten.DegreeDivisible δ ↔ I.DegreeDivisible δ := by
  constructor
  · intro hI v
    simpa only [occurrenceDegree_flatten] using hI (finSumFinEquiv v)
  · intro hI w
    obtain ⟨v, rfl⟩ := finSumFinEquiv.surjective w
    rw [occurrenceDegree_flatten]
    exact hI v
end Instance

/-- Literal ordered partial marginals with a degree certificate on every variable. -/
def PaperDegreeGenerated [CommSemiring K] [Fintype D] {r : ℕ}
    (L : Language D K ι) (δ : ℕ) (G : (Fin r → D) → K) : Prop :=
  ∃ h : ℕ, ∃ I : OrderedInstance L (r + h),
    I.DegreeDivisible δ ∧ ∀ a, I.marginal a = G a

/-- Exact equivalence, with degree preservation proved at the occurrence-list level. -/
theorem degreeGenerated_iff_paperDegreeGenerated [CommSemiring K] [Fintype D] {r δ : ℕ}
    (G : (Fin r → D) → K) : DegreeGenerated L δ G ↔ PaperDegreeGenerated L δ G := by
  constructor
  · rintro ⟨P, hP, rfl⟩
    exact ⟨P.hidden, P.inst.flatten,
      (Instance.degreeDivisible_flatten_iff P.inst δ).mpr hP,
      fun a => Instance.marginal_flatten P.inst a⟩
  · rintro ⟨h, I, hI, hG⟩
    refine ⟨⟨h,I.split⟩,(OrderedInstance.degreeDivisible_split_iff I δ).mpr hI,?_⟩
    funext a
    exact (OrderedInstance.partition_split I a).trans (hG a)

end ComplexCSP
