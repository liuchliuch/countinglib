import ComplexCSP.Recognition.CharacterComparison
import ComplexCSP.Structure.PolynomialPrograms

/-! # Executable universal identities on sparse polynomial programs

Direct and conjugate coordinates are independent formal variables. The oracle
groups equal monomial characters using the corrected all-instance comparator. -/

namespace ComplexCSP.Recognition

open scoped BigOperators

section FiniteCharacterExpressions

variable {D K ι V α : Type} [Field K] [StarRing K] [CharZero K]
variable [Fintype D] [DecidableEq D] [Fintype ι] [Fintype V] [DecidableEq K]

/-- Compute every needed equality by actual finite tensor-target comparison,
then perform the finite coefficient grouping test. -/
def finiteIdentityTest (L : Language D K ι) (s : Finset α)
    (M : α → PinnedMonomial V D) (c : α → K) : Bool :=
  indexedCharacterZeroTest s (fun i j => PinnedMonomial.compare L (M i) (M j)) c

/-- The computed matrix removes the former equality-matrix input hypothesis. -/
theorem finiteIdentityTest_correct (L : Language D K ι) (s : Finset α)
    (M : α → PinnedMonomial V D) (c : α → K) :
    finiteIdentityTest L s M c = true ↔
      ∀ G : GeneratedTable L V, ∑ i ∈ s, c i * (M i).character L G = 0 := by
  exact indexedCharacterZeroTest_correct s (fun i => (M i).character L)
    (fun i j => PinnedMonomial.compare L (M i) (M j)) c
    (fun i _ j _ => PinnedMonomial.compare_correct L (M i) (M j))

end FiniteCharacterExpressions

section ProgramCompilation

variable {D K ι V : Type} {n : ℕ} [CommSemiring K] [StarRing K] [Fintype D]

/-- Expand each finite exponent by literal factor replication. The order is
retained in the tensor coordinates, and repeated factors are not discarded. -/
def termMonomial (coords : Fin n → PinnedCoordinate V D)
    (t : PolynomialPrograms.Term K n) : PinnedMonomial V D :=
  (PolynomialPrograms.expandedVariables t).map coords

/-- The expanded tensor monomial has exactly the intended exponent-vector value. -/
theorem termMonomial_character_apply (L : Language D K ι)
    (coords : Fin n → PinnedCoordinate V D) (t : PolynomialPrograms.Term K n)
    (G : GeneratedTable L V) :
    (termMonomial coords t).character L G =
      ∏ j, (Sum.elim G.val (fun a => star (G.val a)) (coords j)) ^ t.exponent j := by
  rw [PinnedMonomial.character_apply]
  simp only [List.get_eq_getElem, Fin.prod_univ_fun_getElem]
  simpa only [termMonomial, List.map_map, Function.comp_def]
    using PolynomialPrograms.expandedVariables_product t
      (fun j => Sum.elim G.val (fun a => star (G.val a)) (coords j))

/-- The executable sparse-program interpreter is its finite character sum. -/
theorem program_eval_as_character_sum (L : Language D K ι)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n)
    (G : GeneratedTable L V) :
    PolynomialPrograms.eval (fun j => Sum.elim G.val (fun a => star (G.val a))
      (coords j)) P =
      ∑ i : Fin P.length, (P.get i).coefficient *
        (termMonomial coords (P.get i)).character L G := by
  rw [PolynomialPrograms.eval, PolynomialPrograms.interpret_eq_indexed_sum]
  simp only [RingHom.id_apply, termMonomial_character_apply]

end ProgramCompilation

section UniversalProgramOracle

variable {D K ι V : Type} {n : ℕ} [Field K] [StarRing K] [CharZero K]
variable [Fintype D] [DecidableEq D] [Fintype ι] [Fintype V] [DecidableEq K]

/-- A total executable comparison/grouping pipeline for a finite sparse program.
Its inputs are actual finite tables, formal coordinate meanings, and coefficients. -/
def programIdentityTest (L : Language D K ι)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) : Bool :=
  finiteIdentityTest L Finset.univ (fun i : Fin P.length => termMonomial coords (P.get i))
    (fun i => (P.get i).coefficient)

/-- The repaired oracle decides universal vanishing on all actual generated
finite presentations, with direct/conjugate coords kept formally independent. -/
theorem programIdentityTest_correct (L : Language D K ι)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) :
    programIdentityTest L coords P = true ↔
      ∀ Q : Presentation L V,
        PolynomialPrograms.eval (fun j => Sum.elim Q.table (fun a => star (Q.table a))
          (coords j)) P = 0 := by
  rw [programIdentityTest, finiteIdentityTest_correct]
  simp_rw [← program_eval_as_character_sum]
  exact GeneratedTable.forall_iff_presentations (L := L)
    (fun G => PolynomialPrograms.eval (fun j => Sum.elim G (fun a => star (G a))
      (coords j)) P = 0)

/-- Correctness over literal finite instances with canonical hidden-variable indices. -/
theorem programIdentityTest_correct_instances (L : Language D K ι)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) :
    programIdentityTest L coords P = true ↔
      ∀ h : ℕ, ∀ I : Instance L V (Fin h),
        PolynomialPrograms.eval (fun j => Sum.elim I.partition (fun a => star (I.partition a))
          (coords j)) P = 0 := by
  rw [programIdentityTest_correct]
  exact GeneratedTable.forall_presentations_iff_instances
    (fun G => PolynomialPrograms.eval (fun j => Sum.elim G (fun a => star (G a))
      (coords j)) P = 0)

/-- A rejection has a genuine finite presentation whose evaluated polynomial is
nonzero. This does not claim a bound for finding the witness. -/
theorem programIdentityTest_rejects_iff (L : Language D K ι)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) :
    programIdentityTest L coords P = false ↔
      ∃ Q : Presentation L V,
        PolynomialPrograms.eval (fun j => Sum.elim Q.table (fun a => star (Q.table a))
          (coords j)) P ≠ 0 := by
  classical
  rw [← Bool.not_eq_true, programIdentityTest_correct]
  push_neg
  rfl

/-- The same executable decision has exactly the ordinary multivariate-polynomial
meaning of the program's semantic translation. No algorithm calls `denote`. -/
theorem programIdentityTest_mvPolynomial_correct (L : Language D K ι)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) :
    programIdentityTest L coords P = true ↔
      ∀ Q : Presentation L V,
        MvPolynomial.eval (fun j => Sum.elim Q.table (fun a => star (Q.table a))
          (coords j)) (PolynomialPrograms.denote P) = 0 := by
  simp only [← PolynomialPrograms.eval_eq_mvPolynomial_eval]
  exact programIdentityTest_correct L coords P

end UniversalProgramOracle

section DegreeRestrictedProgramOracle

variable {D K ι V α : Type} {n : ℕ} [Field K] [StarRing K] [CharZero K]
variable [Fintype D] [DecidableEq D] [Fintype ι]
variable [Fintype V] [DecidableEq V] [DecidableEq K]

/-- Compute the degree-restricted matrix through actual cyclic augmentation and
finite ordinary target comparisons, then group the input coefficients. -/
def finiteDegreeIdentityTest (L : Language D K ι) (δ : ℕ) (ζ : K)
    (s : Finset α) (M : α → PinnedMonomial V D) (c : α → K) : Bool :=
  indexedCharacterZeroTest s (fun i j => PinnedMonomial.degreeCompare L δ ζ (M i) (M j)) c

theorem finiteDegreeIdentityTest_correct (L : Language D K ι)
    {δ : ℕ} {ζ : K} (hδ : 0 < δ) (hζ : IsPrimitiveRoot ζ δ)
    (s : Finset α) (M : α → PinnedMonomial V D) (c : α → K) :
    finiteDegreeIdentityTest L δ ζ s M c = true ↔
      ∀ G : DegreeGeneratedTable (B := V) L δ,
        ∑ i ∈ s, c i * (M i).degreeCharacter L δ G = 0 := by
  exact indexedCharacterZeroTest_correct s (fun i => (M i).degreeCharacter L δ)
    (fun i j => PinnedMonomial.degreeCompare L δ ζ (M i) (M j)) c
    (fun i _ j _ => PinnedMonomial.degreeCompare_correct L hδ hζ (M i) (M j))

omit [CharZero K] [DecidableEq D] [Fintype ι] [DecidableEq K] in
/-- Sparse polynomial evaluation expands into the actual restricted characters. -/
theorem degree_program_eval_as_character_sum (L : Language D K ι) (δ : ℕ)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n)
    (G : DegreeGeneratedTable (B := V) L δ) :
    PolynomialPrograms.eval (fun j => Sum.elim G.val (fun a => star (G.val a)) (coords j)) P =
      ∑ i : Fin P.length, (P.get i).coefficient *
        (termMonomial coords (P.get i)).degreeCharacter L δ G := by
  exact program_eval_as_character_sum L coords P (DegreeGeneratedTable.inclusion G)

/-- The executable degree-multiple universal identity test. Its field and
primitive root are supplied explicitly; root-field construction is not hidden. -/
def degreeProgramIdentityTest (L : Language D K ι) (δ : ℕ) (ζ : K)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) : Bool :=
  finiteDegreeIdentityTest L δ ζ Finset.univ
    (fun i : Fin P.length => termMonomial coords (P.get i)) (fun i => (P.get i).coefficient)

/-- End-to-end degree-restricted correctness with no equality-matrix input.
Every presentation in the conclusion carries an actual occurrence-degree certificate. -/
theorem degreeProgramIdentityTest_correct (L : Language D K ι)
    {δ : ℕ} {ζ : K} (hδ : 0 < δ) (hζ : IsPrimitiveRoot ζ δ)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) :
    degreeProgramIdentityTest L δ ζ coords P = true ↔
      ∀ Q : Presentation L V, Q.DegreeDivisible δ →
        PolynomialPrograms.eval (fun j => Sum.elim Q.table (fun a => star (Q.table a))
          (coords j)) P = 0 := by
  rw [degreeProgramIdentityTest, finiteDegreeIdentityTest_correct L hδ hζ]
  simp_rw [← degree_program_eval_as_character_sum]
  exact DegreeGeneratedTable.forall_iff_presentations (L := L) (δ := δ)
    (fun G => PolynomialPrograms.eval (fun j => Sum.elim G (fun a => star (G a))
      (coords j)) P = 0)

/-- An exact literal-instance formulation of the same degree-restricted algorithm. -/
theorem degreeProgramIdentityTest_correct_instances (L : Language D K ι)
    {δ : ℕ} {ζ : K} (hδ : 0 < δ) (hζ : IsPrimitiveRoot ζ δ)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) :
    degreeProgramIdentityTest L δ ζ coords P = true ↔
      ∀ h : ℕ, ∀ I : Instance L V (Fin h), I.DegreeDivisible δ →
        PolynomialPrograms.eval (fun j => Sum.elim I.partition (fun a => star (I.partition a))
          (coords j)) P = 0 := by
  rw [degreeProgramIdentityTest_correct L hδ hζ]
  exact DegreeGeneratedTable.forall_presentations_iff_instances
    (fun G => PolynomialPrograms.eval (fun j => Sum.elim G (fun a => star (G a))
      (coords j)) P = 0)

/-- Every degree-restricted rejection has a real finite counterexample with the
required degree certificate. No counterexample-size bound is asserted. -/
theorem degreeProgramIdentityTest_rejects_iff (L : Language D K ι)
    {δ : ℕ} {ζ : K} (hδ : 0 < δ) (hζ : IsPrimitiveRoot ζ δ)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) :
    degreeProgramIdentityTest L δ ζ coords P = false ↔
      ∃ Q : Presentation L V, Q.DegreeDivisible δ ∧
        PolynomialPrograms.eval (fun j => Sum.elim Q.table (fun a => star (Q.table a))
          (coords j)) P ≠ 0 := by
  classical
  rw [← Bool.not_eq_true, degreeProgramIdentityTest_correct L hδ hζ]
  push_neg
  rfl

/-- The computed answer agrees with the ordinary MvPolynomial semantics without
calling the noncomputable polynomial translation during execution. -/
theorem degreeProgramIdentityTest_mvPolynomial_correct (L : Language D K ι)
    {δ : ℕ} {ζ : K} (hδ : 0 < δ) (hζ : IsPrimitiveRoot ζ δ)
    (coords : Fin n → PinnedCoordinate V D) (P : PolynomialPrograms.Program K n) :
    degreeProgramIdentityTest L δ ζ coords P = true ↔
      ∀ Q : Presentation L V, Q.DegreeDivisible δ →
        MvPolynomial.eval (fun j => Sum.elim Q.table (fun a => star (Q.table a))
          (coords j)) (PolynomialPrograms.denote P) = 0 := by
  simp only [← PolynomialPrograms.eval_eq_mvPolynomial_eval]
  exact degreeProgramIdentityTest_correct L hδ hζ coords P

end DegreeRestrictedProgramOracle

end ComplexCSP.Recognition
