import ComplexCSP.Recognition.GeneratedDetector
import ComplexCSP.Instances.PresentationAlgorithms
import ComplexCSP.Instances.ValueTransport
import ComplexCSP.Structure.RowTypes
import ComplexCSP.Structure.RowPhases

/-! # Executable row tests and literal two-copy detector presentations

The compiler retains independent hidden copies, identifies only intended row and
column positions, then sums the shared column. Tests use finite field arithmetic,
not complex proportionality or purification oracles.
-/
namespace ComplexCSP
open scoped BigOperators

namespace RowTypes
variable {D K R : Type*} [Fintype D] [Field K] [DecidableEq K]

/-- Finite arithmetic test for two nonzero proportional rows. -/
def nonzeroProportionalTest (u v : D → K) : Bool :=
  decide ((∃ z, u z ≠ 0) ∧ (∃ z, v z ≠ 0) ∧ ∀ z w, u z * v w = u w * v z)

 theorem nonzeroProportionalTest_correct (u v : D → K) :
    nonzeroProportionalTest u v = true ↔ u ≠ 0 ∧ v ≠ 0 ∧ Proportional u v := by
  simp only [nonzeroProportionalTest,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨i,hi⟩,⟨j,hj⟩,hm⟩
    have huj : u j ≠ 0 := by
      intro h
      have he := hm i j
      rw [h,zero_mul] at he
      exact (mul_ne_zero hi hj) he
    refine ⟨?_,?_,u j / v j,div_ne_zero huj hj,?_⟩
    · intro h
      exact hi (congrFun h i)
    · intro h
      exact hj (congrFun h j)
    · intro z
      apply (mul_right_cancel₀ hj)
      calc
        u z * v j = u j * v z := hm z j
        _ = (u j / v j * v z) * v j := by field_simp
  · rintro ⟨hu,hv,c,hc,h⟩
    have he (f : D → K) (hf : f ≠ 0) : ∃ i, f i ≠ 0 := by
      by_contra! hn
      exact hf (funext hn)
    refine ⟨he u hu,he v hv,?_⟩
    intro z w
    rw [h z,h w]
    ring

 theorem nonzeroProportionalTest_map [Field R] [DecidableEq R]
    (σ : K →+* R) (u v : D → K) :
    nonzeroProportionalTest (fun z => σ (u z)) (fun z => σ (v z)) =
      nonzeroProportionalTest u v := by
  unfold nonzeroProportionalTest
  congr 1
  simp only [map_ne_zero,← map_mul,σ.injective.eq_iff]

end RowTypes

namespace Presentation
variable {D K ι : Type} {L : Language D K ι} {n : ℕ}

def detectorLeftFinScope (n : ℕ) : Fin (n+1) → Fin (n+n) ⊕ Fin 1 :=
  Fin.lastCases (Sum.inr 0) (fun i => Sum.inl (Fin.castAdd n i))

def detectorRightFinScope (n : ℕ) : Fin (n+1) → Fin (n+n) ⊕ Fin 1 :=
  Fin.lastCases (Sum.inr 0) (fun i => Sum.inl (Fin.natAdd n i))

@[simp] theorem detectorLeftFin_assignment (a : Fin (n+n) → D) (b : Fin 1 → D) :
    Sum.elim a b ∘ detectorLeftFinScope n =
      Fin.snoc (fun i => a (Fin.castAdd n i)) (b 0) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [detectorLeftFinScope]

@[simp] theorem detectorRightFin_assignment (a : Fin (n+n) → D) (b : Fin 1 → D) :
    Sum.elim a b ∘ detectorRightFinScope n =
      Fin.snoc (fun i => a (Fin.natAdd n i)) (b 0) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [detectorRightFinScope]

/-- The actual finite presentation of the displayed two-copy detector. -/
def rowDetector (P : Presentation L (Fin (n+1))) (p q : ℕ) :
    Presentation L (Fin (n+n)) :=
  (((P.power p).rename (detectorLeftFinScope n)).mul
    ((P.power q).rename (detectorRightFinScope n))).marginal

@[simp] theorem table_rowDetector [CommSemiring K] [Fintype D]
    (P : Presentation L (Fin (n+1))) (p q : ℕ) :
    (P.rowDetector p q).table = ComplexCSP.rowDetector P.table p q := by
  funext a
  simp only [rowDetector,table_marginal,table_mul,table_rename,table_power,
    detectorLeftFin_assignment,detectorRightFin_assignment,ComplexCSP.rowDetector]
  exact (Equiv.funUnique (Fin 1) D).sum_comp (fun z =>
    P.table (Fin.snoc (fun i => a (Fin.castAdd n i)) z) ^ p *
      P.table (Fin.snoc (fun i => a (Fin.natAdd n i)) z) ^ q)

end Presentation

/-- Field embeddings commute with every entry of the detector. -/
theorem rowDetector_map {D K R : Type} [Fintype D] [CommSemiring K] [CommSemiring R]
    {n : ℕ} (σ : K →+* R) (G : (Fin (n+1) → D) → K) (p q : ℕ)
    (a : Fin (n+n) → D) :
    rowDetector (fun b => σ (G b)) p q a = σ (rowDetector G p q a) := by
  simp only [rowDetector,map_sum,map_mul,map_pow]

namespace RowDetector
variable {D K : Type} [Fintype D] [Field K] [DecidableEq K]
variable {n : ℕ}

/-- Exact finite test of the entire desired support relation at one allowed time. -/
def detectorTimeTest (G : (Fin (n+1) → D) → K) (E t : ℕ) : Bool :=
  let q := 1 + RowPhases.phaseExponent (Fintype.card D) * t
  decide (∀ a : Fin (n+n) → D,
    rowDetector G ((E-1)*q) q a ≠ 0 ↔
      RowTypes.nonzeroProportionalTest
        (fun z => G (Fin.snoc (fun i => a (Fin.castAdd n i)) z))
        (fun z => G (Fin.snoc (fun i => a (Fin.natAdd n i)) z)) = true)

/-- The test is exactly the original complex Ω support, through any genuine
field embedding. Complex equality is used only in this semantic theorem. -/
theorem detectorTimeTest_correct (G : (Fin (n+1) → D) → K) (E t : ℕ) (σ : K →+* ℂ) :
    detectorTimeTest G E t = true ↔
      ∀ a : Fin (n+n) → D,
        rowDetector (fun b => σ (G b))
          ((E-1)*(1+RowPhases.phaseExponent (Fintype.card D)*t))
          (1+RowPhases.phaseExponent (Fintype.card D)*t) a ≠ 0 ↔
          a ∈ (RowTypes.omegaRelation (fun b => σ (G b))).tuples := by
  classical
  simp only [detectorTimeTest,decide_eq_true_eq,RowTypes.omegaRelation,
    Set.mem_ofPred_eq,RowTypes.Omega,RowTypes.NonzeroProportionalRows]
  apply forall_congr'
  intro a
  rw [rowDetector_map,map_ne_zero]
  change (_ ↔ _) ↔ (_ ↔ _ ≠ 0 ∧ _ ≠ 0 ∧ RowTypes.Proportional _ _)
  rw [← RowTypes.nonzeroProportionalTest_correct]
  have hm := RowTypes.nonzeroProportionalTest_map σ
    (fun z => G (Fin.snoc (fun i => a (Fin.castAdd n i)) z))
    (fun z => G (Fin.snoc (fun i => a (Fin.natAdd n i)) z))
  exact iff_congr Iff.rfl ((congrArg (fun b : Bool => b = true) hm).symm.to_iff)

/-- Actual exact search from a proved existence argument. Public validated
frontends derive that argument from global BO and computed torsion data. -/
def findTableDetectorTime (G : (Fin (n+1) → D) → K) (E : ℕ)
    (h : ∃ t, detectorTimeTest G E t = true) : ℕ := Nat.find h

 theorem findTableDetectorTime_spec (G : (Fin (n+1) → D) → K) (E : ℕ)
    (h : ∃ t, detectorTimeTest G E t = true) :
    detectorTimeTest G E (findTableDetectorTime G E h) = true := Nat.find_spec h

end RowDetector

end ComplexCSP
