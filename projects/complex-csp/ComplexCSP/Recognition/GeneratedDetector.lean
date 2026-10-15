import ComplexCSP.Instances.OrderedInstances

/-! # Literal generated row detector

The two powered copies share only the intended retained row variables and the
summed final coordinate. Their previously hidden variables are disjoint by the
proved gluing/power construction. No conjugated constraint symbol is introduced.
-/
namespace ComplexCSP
open scoped BigOperators

variable {D K ι : Type} {L : Language D K ι} {n : ℕ}

/-- Attach one copy to the first row variables, retaining the final column. -/
def detectorLeftScope (n : ℕ) : Fin (n + 1) → Fin (n + n) ⊕ Unit :=
  Fin.lastCases (Sum.inr ()) (fun i => Sum.inl (Fin.castAdd n i))

/-- Attach the other copy to the second row variables and the same column. -/
def detectorRightScope (n : ℕ) : Fin (n + 1) → Fin (n + n) ⊕ Unit :=
  Fin.lastCases (Sum.inr ()) (fun i => Sum.inl (Fin.natAdd n i))

@[simp] theorem detectorLeft_assignment (a : Fin (n + n) → D) (b : Unit → D) :
    Sum.elim a b ∘ detectorLeftScope n =
      Fin.snoc (fun i => a (Fin.castAdd n i)) (b ()) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [detectorLeftScope]
  · simp [detectorLeftScope]

@[simp] theorem detectorRight_assignment (a : Fin (n + n) → D) (b : Unit → D) :
    Sum.elim a b ∘ detectorRightScope n =
      Fin.snoc (fun i => a (Fin.natAdd n i)) (b ()) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [detectorRightScope]
  · simp [detectorRightScope]

/-- The concrete two-row detector, for arbitrary natural exponents. -/
def rowDetector [CommSemiring K] [Fintype D]
    (G : (Fin (n + 1) → D) → K) (p q : ℕ) (a : Fin (n + n) → D) : K :=
  ∑ z : D, G (Fin.snoc (fun i => a (Fin.castAdd n i)) z) ^ p *
    G (Fin.snoc (fun i => a (Fin.natAdd n i)) z) ^ q

/-- The detector really belongs to the full generated family. -/
theorem generated_rowDetector [CommSemiring K] [Fintype D]
    {G : (Fin (n + 1) → D) → K} (hG : Instance.Generated L G) (p q : ℕ) :
    Instance.Generated L (rowDetector G p q) := by
  let F := fun a : Fin (n + n) ⊕ Unit → D =>
    G (a ∘ detectorLeftScope n) ^ p * G (a ∘ detectorRightScope n) ^ q
  have hF : Instance.Generated L F :=
    Instance.generated_mul
      (Instance.generated_pow (Instance.generated_diagonal_minor hG (detectorLeftScope n)) p)
      (Instance.generated_pow (Instance.generated_diagonal_minor hG (detectorRightScope n)) q)
  have hm := Instance.generated_marginal hF
  have he : (fun a => ∑ b : Unit → D, F (Sum.elim a b)) = rowDetector G p q := by
    funext a
    simp only [F, detectorLeft_assignment, detectorRight_assignment, rowDetector]
    exact (Equiv.funUnique Unit D).sum_comp (fun z =>
      G (Fin.snoc (fun i => a (Fin.castAdd n i)) z) ^ p *
      G (Fin.snoc (fun i => a (Fin.natAdd n i)) z) ^ q)
  rwa [he] at hm

/-- The finite-instance construction in Theorem 8.4, under the exact ordered
semantics. Support equality with Ω is a separate mathematical theorem. -/
theorem paper_generated_rowDetector [CommSemiring K] [Fintype D]
    {G : (Fin (n + 1) → D) → K} (hG : PaperGenerated L G) (p q : ℕ) :
    PaperGenerated L (rowDetector G p q) :=
  (generated_iff_paperGenerated _).mp
    (generated_rowDetector ((generated_iff_paperGenerated _).mpr hG) p q)

end ComplexCSP
