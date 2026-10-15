import ComplexCSP.Recognition.DegreeGenerated

/-! # Literal fixed-gadget substitution (Lin 2021, Lemma 7)

Each derived constraint is replaced by its actual base-language presentation.
Boundary scope positions may repeat; hidden variables of different copies are
kept disjoint. The original variable set, including isolated variables, is
retained before marginalization. All definitions below are executable finite
syntax operations; no gadget-substitution oracle is supplied.
-/
namespace ComplexCSP.GadgetSubstitution
open scoped BigOperators

variable {D K ι κ B : Type} {L : Language D K ι} {M : Language D K κ}

/-- Fixed presentation data for each symbol of the derived language. -/
abbrev Gadgets (L : Language D K ι) (M : Language D K κ) :=
  (j : κ) → Presentation L (Fin (M.arity j))

/-- One literal replacement, keeping the actual ordered scope. -/
def atom (P : Gadgets L M) {V : Type} (c : Constraint M V) : Presentation L V :=
  (P c.symbol).rename c.scope

/-- Independent copies for the entire source constraint list. All original
variables are retained as boundary variables, including isolated ones. -/
def expand (P : Gadgets L M) {h : ℕ} (I : Instance M B (Fin h)) :
    Presentation L (B ⊕ Fin h) :=
  Presentation.product (I.constraints.map (atom P))

/-- The concrete substitution compiler with canonically indexed hidden variables. -/
def compile (P : Gadgets L M) {h : ℕ} (I : Instance M B (Fin h)) : Presentation L B :=
  (expand P I).marginal

/-- The derived signature is exactly the gadget's pinned partition table. -/
def Realizes [CommSemiring K] [Fintype D] (P : Gadgets L M) : Prop :=
  ∀ j a, (P j).table a = M.value j a

@[simp] theorem table_atom [CommSemiring K] [Fintype D]
    (P : Gadgets L M) (hP : Realizes P) {V : Type} (c : Constraint M V) (a : V → D) :
    (atom P c).table a = c.eval a := by
  rw [atom, Presentation.table_rename, hP]
  rfl

/-- Summing precisely the newly introduced hidden variables gives the original
constraint product for every assignment of the original variables. -/
theorem table_expand [CommSemiring K] [Fintype D]
    (P : Gadgets L M) (hP : Realizes P) {h : ℕ} (I : Instance M B (Fin h))
    (a : B → D) (b : Fin h → D) :
    (expand P I).table (Sum.elim a b) = I.eval a b := by
  simp only [expand, Presentation.table_product, List.map_map, Function.comp_def, table_atom P hP]
  rfl

/-- Exact partition-value preservation, including repeated constraints, repeated
scope positions, cancellation, and isolated original variables. -/
theorem table_compile [CommSemiring K] [Fintype D]
    (P : Gadgets L M) (hP : Realizes P) {h : ℕ} (I : Instance M B (Fin h)) (a : B → D) :
    (compile P I).table a = I.partition a := by
  simp only [compile, Presentation.table_marginal, table_expand P hP, Instance.partition]

/-- Every occurrence degree after substitution is divisible by δ. No source
instance degree condition is needed for Lin's unrestricted-to-restricted transfer. -/
theorem degreeDivisible_compile [Fintype B] [DecidableEq B]
    (P : Gadgets L M) (δ : ℕ) (hP : ∀ j, (P j).DegreeDivisible δ)
    {h : ℕ} (I : Instance M B (Fin h)) : (compile P I).DegreeDivisible δ := by
  apply Presentation.DegreeDivisible.marginal
  apply Presentation.degreeDivisible_product
  intro Q hQ
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp hQ
  exact (hP c.symbol).rename c.scope

/-- Syntactic size charges hidden variables, constraints and every scope position. -/
def size {V : Type} (Q : Presentation L V) : ℕ :=
  Q.hidden + Q.inst.constraints.length + Q.inst.occurrences.length

@[simp] theorem size_one {V : Type} : size (Presentation.one : Presentation L V) = 0 := by
  simp [size, Presentation.one, Instance.occurrences]

@[simp] theorem size_rename {V W : Type} (Q : Presentation L V) (f : V → W) :
    size (Q.rename f) = size Q := by
  have ho : (Q.inst.renameBoundary f).occurrences.length = Q.inst.occurrences.length := by
    change (Q.inst.mapVariables (Sum.map f id)).occurrences.length = _
    rw [Instance.occurrences_mapVariables, List.length_map]
  simpa only [size, Presentation.rename, Instance.renameBoundary, List.length_map] using
    congrArg (fun n => Q.hidden + Q.inst.constraints.length + n) ho

@[simp] theorem size_mul {V : Type} (Q R : Presentation L V) :
    size (Q.mul R) = size Q + size R := by
  have hrename (I : Instance L V (Fin Q.hidden ⊕ Fin R.hidden)) :
      (I.renameHidden finSumFinEquiv).occurrences.length = I.occurrences.length := by
    change (I.mapVariables (Sum.map id finSumFinEquiv)).occurrences.length = _
    rw [Instance.occurrences_mapVariables, List.length_map]
  have hq : (Q.inst.renameHidden (Sum.inl : Fin Q.hidden → Fin Q.hidden ⊕ Fin R.hidden)).occurrences.length =
      Q.inst.occurrences.length := by
    change (Q.inst.mapVariables (Sum.map id Sum.inl)).occurrences.length = _
    rw [Instance.occurrences_mapVariables, List.length_map]
  have hr : (R.inst.renameHidden (Sum.inr : Fin R.hidden → Fin Q.hidden ⊕ Fin R.hidden)).occurrences.length =
      R.inst.occurrences.length := by
    change (R.inst.mapVariables (Sum.map id Sum.inr)).occurrences.length = _
    rw [Instance.occurrences_mapVariables, List.length_map]
  unfold size Presentation.mul
  rw [hrename, Instance.occurrences_glue, List.length_append, hq, hr]
  simp only [Instance.renameHidden, List.length_map, Instance.glue, List.length_append]
  omega

@[simp] theorem size_product {V : Type} (Qs : List (Presentation L V)) :
    size (Presentation.product Qs) = (Qs.map size).sum := by
  induction Qs with
  | nil => simp [Presentation.product]
  | cons Q Qs ih => simp only [Presentation.product, size_mul, ih, List.map_cons, List.sum_cons]

@[simp] theorem size_marginal {h : ℕ} (Q : Presentation L (B ⊕ Fin h)) :
    size Q.marginal = h + size Q := by
  have hrename : (Q.inst.hideBoundary.renameHidden finSumFinEquiv).occurrences.length =
      Q.inst.hideBoundary.occurrences.length := by
    change (Q.inst.hideBoundary.mapVariables (Sum.map id finSumFinEquiv)).occurrences.length = _
    rw [Instance.occurrences_mapVariables, List.length_map]
  have hhide : Q.inst.hideBoundary.occurrences.length = Q.inst.occurrences.length := by
    change (Q.inst.mapVariables (Equiv.sumAssoc B (Fin h) (Fin Q.hidden))).occurrences.length = _
    rw [Instance.occurrences_mapVariables, List.length_map]
  unfold size Presentation.marginal
  rw [hrename, hhide]
  simp only [Instance.renameHidden, Instance.hideBoundary, List.length_map]
  omega

/-- Exact size formula: no variable or occurrence is silently deduplicated. -/
theorem size_compile (P : Gadgets L M) {h : ℕ} (I : Instance M B (Fin h)) :
    size (compile P I) = h + (I.constraints.map (fun c => size (P c.symbol))).sum := by
  simp only [compile, size_marginal, expand, size_product, List.map_map, Function.comp_def, atom, size_rename]

/-- A fixed finite language supplies a concrete constant size bound. -/
def gadgetBound [Fintype κ] (P : Gadgets L M) : ℕ := ∑ j, size (P j)

/-- Explicit linear syntactic bound in the source variable and constraint counts. -/
theorem size_compile_le [Fintype κ] (P : Gadgets L M) {h : ℕ}
    (I : Instance M B (Fin h)) :
    size (compile P I) ≤ h + gadgetBound P * I.constraints.length := by
  rw [size_compile]
  apply Nat.add_le_add_left
  have hb (c : Constraint M (B ⊕ Fin h)) : size (P c.symbol) ≤ gadgetBound P :=
    Finset.single_le_sum (f := fun j => size (P j)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ c.symbol)
  induction I.constraints with
  | nil => simp
  | cons c cs ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_add, Nat.mul_one]
    have := hb c
    omega

/-- Adding retained original variables gives the full finite-instance size bound. -/
theorem total_size_compile_le [Fintype B] [Fintype κ] (P : Gadgets L M) {h : ℕ}
    (I : Instance M B (Fin h)) :
    Fintype.card B + size (compile P I) ≤
      Fintype.card B + h + gadgetBound P * I.constraints.length := by
  have := size_compile_le P I
  omega

end ComplexCSP.GadgetSubstitution
