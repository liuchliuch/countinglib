import Paper2.ExactInput.FixedRootCodec.VariableRootBisectionBounds
import Mathlib.Data.Finset.Sort

/-! Canonical real-root semantics for the generic actual refinement programs.
The mathematical root count uses the distinct roots of the input polynomial;
sorting and its finite capacity are proved here. The final Sturm program still
has to prove that its actual numerical result is this count. -/
namespace Paper2.ExactInput.FixedRootCodec.VariableRootBisection
open Computability Paper2.Algebraic Paper2.Complexity Polynomial
open BinaryCompose FixedFieldMachines BellMachines GraphPreprocessing
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def realRootSet (v : Fin n → ℚ) : Finset ℝ :=
  ((VariablePolynomial.polynomial v).map (algebraMap ℚ ℝ)).roots.toFinset

def realRootCount (v : Fin n → ℚ) (q : ℚ) : ℕ := by
  classical
  exact ((realRootSet v).filter (fun r => r ≤ (q : ℝ))).card

def orderedRealRoots (v : Fin n → ℚ) : Fin (realRootSet v).card ↪o ℝ :=
  (realRootSet v).orderEmbOfFin rfl

theorem realRootSet_mem_iff (v : Fin n → ℚ) (hp : VariablePolynomial.polynomial v ≠ 0)
    (r : ℝ) : r ∈ realRootSet v ↔ (VariablePolynomial.polynomial v).aeval r = 0 := by
  rw [realRootSet,Multiset.mem_toFinset,Polynomial.mem_roots (Polynomial.map_ne_zero hp),
    Polynomial.IsRoot,Polynomial.eval_map]
  rfl

theorem orderedRealRoots_root (v : Fin n → ℚ) (hp : VariablePolynomial.polynomial v ≠ 0)
    (i : Fin (realRootSet v).card) :
    (VariablePolynomial.polynomial v).aeval (orderedRealRoots v i) = 0 :=
  (realRootSet_mem_iff v hp _).mp ((realRootSet v).orderEmbOfFin_mem rfl i)

theorem sortedPrefixCount_ordered (v : Fin n → ℚ) (q : ℚ) :
    sortedPrefixCount (orderedRealRoots v) q = realRootCount v q := by
  classical
  let emb := (orderedRealRoots v).toEmbedding
  have he : Finset.univ.map emb = realRootSet v :=
    (realRootSet v).map_orderEmbOfFin_univ rfl
  have hf : (Finset.univ.filter (fun i => orderedRealRoots v i ≤ (q : ℝ))).map emb =
      (realRootSet v).filter (fun r => r ≤ (q : ℝ)) := by
    calc
      _ = (Finset.univ.map emb).filter (fun r => r ≤ (q : ℝ)) := by
        rw [Finset.filter_map]
        rfl
      _ = _ := congrArg (fun S : Finset ℝ => S.filter (fun r => r ≤ (q : ℝ))) he
  have hc := congrArg Finset.card hf
  rw [Finset.card_map] at hc
  exact hc

theorem realRootCount_threshold (v : Fin n → ℚ) (j : Fin (realRootSet v).card) (q : ℚ) :
    realRootCount v q ≤ j.val ↔ (q : ℝ) < orderedRealRoots v j := by
  rw [← sortedPrefixCount_ordered]
  exact sortedPrefixCount_le_iff (orderedRealRoots v) (orderedRealRoots v).strictMono j q

theorem realRootSet_card_le (v : Fin n → ℚ) (hp : VariablePolynomial.polynomial v ≠ 0) :
    (realRootSet v).card ≤ n :=
  sorted_root_slots_bound v hp (orderedRealRoots v) (orderedRealRoots v).strictMono
    (orderedRealRoots_root v hp)

theorem real_root_has_rank (v : Fin n → ℚ) (hp : VariablePolynomial.polynomial v ≠ 0)
    (r : ℝ) (hr : (VariablePolynomial.polynomial v).aeval r = 0) :
    ∃ j : Fin (realRootSet v).card, orderedRealRoots v j = r := by
  have hm := (realRootSet_mem_iff v hp r).mpr hr
  have h : r ∈ Set.range (orderedRealRoots v) := by
    rw [orderedRealRoots,Finset.range_orderEmbOfFin]
    exact hm
  exact h

/-- The actual rational array covers every distinct real root, once the actual
count program is identified with the input polynomial's finite prefix count. -/
theorem approximationVector_cover (count : CountFunction n) (v : Fin n → ℚ)
    (hp : VariablePolynomial.polynomial v ≠ 0)
    (hcount : ∀ q : ℚ, count v q = realRootCount v q) (t : ℕ)
    (r : ℝ) (hr : (VariablePolynomial.polynomial v).aeval r = 0) :
    ∃ j : Fin n, active count j.val v = true ∧
      |(approximate count j.val t v : ℝ)-r| < 1/(2 : ℝ)^t := by
  obtain ⟨j,hj⟩ := real_root_has_rank v hp r hr
  let index : Fin n := ⟨j.val,lt_of_lt_of_le j.isLt (realRootSet_card_le v hp)⟩
  have hs : ∀ q : ℚ, count v q = sortedPrefixCount (orderedRealRoots v) q := by
    intro q
    rw [hcount q,sortedPrefixCount_ordered]
  refine ⟨index,?_,?_⟩
  · exact (active_iff_rank count v hp (orderedRealRoots v) (orderedRealRoots_root v hp)
      hs j.val).mpr j.isLt
  · have he := sorted_root_approximate_error count v hp (orderedRealRoots v)
      (orderedRealRoots v).strictMono (orderedRealRoots_root v hp) hs j t
    rw [hj] at he
    exact he

def approximationsOutputBound (count : CountFunction n)
    (w : Computes (VariablePolynomial.inputEncoding n) encodingNatBool
      (fun p => count p.1 p.2)) :
    PolynomialOutputBound (requestEncoding n) (framedListEncoding slotEncoding)
      (fun p => approximations count p.1 p.2) :=
  (approximationsComputes count w).outputBound

def approximationVectorOutputBound (count : CountFunction n)
    (w : Computes (VariablePolynomial.inputEncoding n) encodingNatBool
      (fun p => count p.1 p.2)) :
    PolynomialOutputBound (requestEncoding n) (vectorEncoding n)
      (fun p j => approximate count j.val p.1 p.2) :=
  (approximationVectorComputes count w).outputBound

end
end Paper2.ExactInput.FixedRootCodec.VariableRootBisection
