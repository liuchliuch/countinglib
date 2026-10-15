import Paper2.Paper1Accepted.DiagonalSlices
import Holant.ReedMuller.DiagonalSlice.Source

/-! The precise Paper 1 diagonal-slice interface supplied by its frozen Lean
proof. Nonzero complex coefficients are lifted to units, and every unary
restriction is transported literally to the source equal-coordinate form. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open scoped BigOperators

private lemma prod_split_two {r : ℕ} (u : Fin r → ℂ) (i j : Fin r) (hij : i ≠ j) :
    (∏ k, u k) = u i * u j * ∏ k ∈ Holant.ReedMuller.DiagonalSlice.outside i j, u k := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ u (Finset.mem_univ i),
    ← Finset.mul_prod_erase (Finset.univ.erase i) u (a := j) (by simp [hij.symm])]
  simp only [Holant.ReedMuller.DiagonalSlice.outside,mul_assoc]

private def unitTable {r : ℕ} (h : Signature ℂ r) (hn : ∀ x,h x ≠ 0) :
    (Fin r → Bool) → ℂˣ := fun x => Units.mk0 (h x) (hn x)

private lemma unitTable_zero {r : ℕ} (h : Signature ℂ r) (hn : ∀ x,h x ≠ 0)
    (h0 : h (fun _ => false) = 1) : unitTable h hn (fun _ => false) = 1 := by
  apply Units.ext
  exact h0

private lemma unitTable_simple {r : ℕ} (h : Signature ℂ r) (hn : ∀ x,h x ≠ 0)
    (hd : DiagonalSlices.UnaryDiagonals h) (i j : Fin r) (hij : i ≠ j) :
    Holant.ReedMuller.DiagonalSlice.SimpleDiagonal (unitTable h hn) i j := by
  classical
  obtain ⟨c,u,hc,hu,he⟩ := hd i j hij
  refine ⟨fun b => Units.mk0 (c * u i b * u j b)
    (mul_ne_zero (mul_ne_zero hc (hu i b)) (hu j b)),
    fun k b => Units.mk0 (u k b) (hu k b), ?_⟩
  intro x ht
  apply Units.ext
  simp only [unitTable,Units.val_mk0,Units.val_mul,Units.coe_prod]
  rw [he x ht,prod_split_two (fun k => u k (x k)) i j hij,← ht]
  ring

private lemma singleWord_source {r : ℕ} (i : Fin r) :
    DiagonalSlices.singleWord i = Holant.ReedMuller.DiagonalSlice.word {i} := by
  classical
  funext k
  simp [DiagonalSlices.singleWord,Holant.ReedMuller.DiagonalSlice.word]

private lemma doubleWord_source {r : ℕ} (i j : Fin r) :
    DiagonalSlices.doubleWord i j = Holant.ReedMuller.DiagonalSlice.word {i,j} := by
  classical
  funext k
  simp [DiagonalSlices.doubleWord,Holant.ReedMuller.DiagonalSlice.word]

/-- Both exact clauses of source Lemma 7.8, including its nontrivial three-port
exception, are supplied by the existing frozen Paper 1 integration proof. -/
def provedDiagonalSlices : Paper1DiagonalSlicesAccepted where
  diagonal_large_7_8 r hr h hn h0 hd := by
    classical
    obtain ⟨ρ,H⟩ := Holant.ReedMuller.DiagonalSlice.diagonal_slice_integration hr
      (unitTable h hn) (unitTable_zero h hn h0) (unitTable_simple h hn hd)
    refine ⟨fun i => (ρ i : ℂ),fun i => Units.ne_zero (ρ i),?_⟩
    intro x
    have hh := congrArg (fun z : ℂˣ => (z : ℂ)) (H x)
    simp only [unitTable,Units.val_mk0,Units.coe_prod,Units.val_pow_eq_pow_val] at hh
    convert hh using 1
    apply Finset.prod_congr rfl
    intro i hi
    cases x i <;> simp
  diagonal_three_7_8 h hn h0 hd := by
    classical
    obtain ⟨ρ,κ,hs,hd,hall⟩ := Holant.ReedMuller.DiagonalSlice.diagonal_slice_three
      (unitTable h hn) (unitTable_zero h hn h0) (unitTable_simple h hn hd)
    refine ⟨fun i => (ρ i : ℂ),(κ : ℂ),fun i => Units.ne_zero (ρ i),Units.ne_zero κ,?_,?_,?_⟩
    · intro i
      have hh := congrArg (fun z : ℂˣ => (z : ℂ)) (hs i)
      simpa only [unitTable,Units.val_mk0,← singleWord_source] using hh
    · intro i j hij
      have hh := congrArg (fun z : ℂˣ => (z : ℂ)) (hd i j hij)
      simpa only [unitTable,Units.val_mk0,Units.val_mul,← doubleWord_source] using hh
    · have hh := congrArg (fun z : ℂˣ => (z : ℂ)) hall
      simpa only [unitTable,Units.val_mk0,Units.val_mul,Fin.prod_univ_three,mul_assoc] using hh

end
end Paper2.HeightOne.PhaseCards

