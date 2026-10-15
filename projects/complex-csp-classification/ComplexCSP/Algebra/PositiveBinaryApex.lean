import ComplexCSP.Complexity.CSPCode

/-! # A genuine general-graph two-spin hardness bridge: shared-apex algebra

For an equal-diagonal symmetric two-spin interaction, one shared apex turns
its graph partition into twice the partition for a biased interaction. The
apex is shared across all edge occurrences, so the construction is allowed on
general graphs and is not claimed to preserve planarity.
-/
namespace ComplexCSP

namespace MatrixCSP

def language {D K : Type} (A : D → D → K) : Language D K (Fin 1) :=
  ⟨fun _ => 2, fun _ => Nat.succ_pos 1, fun _ a => A (a 0) (a 1)⟩

end MatrixCSP
namespace PositiveBinaryApex
open scoped BigOperators

variable {K : Type}

section Ring
variable [CommRing K]

/-- The effective edge matrix with the shared apex pinned to false. -/
def biased (A : Bool → Bool → K) (i j : Bool) : K :=
  A i j * A i false * A j false

theorem biased_symmetric (A : Bool → Bool → K) (hs : ∀ i j, A i j = A j i) :
    ∀ i j, biased A i j = biased A j i := by
  intro i j
  rw [biased,biased,hs i j]
  ring

omit [CommRing K] in
theorem flip_invariant (A : Bool → Bool → K)
    (hs : ∀ i j, A i j = A j i) (hd : A false false = A true true) :
    ∀ i j, A (!i) (!j) = A i j := by
  intro i j
  cases i <;> cases j <;> simp only [Bool.not_false,Bool.not_true]
  · exact hd.symm
  · exact hs _ _
  · exact hs _ _
  · exact hd

/-- Pinning the apex to true gives the same effective interaction after a
simultaneous spin flip of every original vertex. -/
theorem triangle_true (A : Bool → Bool → K)
    (hs : ∀ i j, A i j = A j i) (hd : A false false = A true true) (i j : Bool) :
    A i j * A i true * A j true = biased A (!i) (!j) := by
  have hf := flip_invariant A hs hd
  rw [biased, hf i j, ← hf i true, ← hf j true]
  rfl

/-- Literal graph product for a list of ordered edge occurrences. -/
def graphWeight {V : Type} (A : Bool → Bool → K) (edges : List (V × V)) (σ : V → Bool) : K :=
  (edges.map (fun e => A (σ e.1) (σ e.2))).prod

/-- Exact shared-apex partition identity, preserving loops, duplicate edges,
isolated vertices and the empty graph. -/
theorem shared_apex_partition {V : Type} [Fintype V] [DecidableEq V]
    (A : Bool → Bool → K) (hs : ∀ i j, A i j = A j i)
    (hd : A false false = A true true) (edges : List (V × V)) :
    (∑ σ : V → Bool, ∑ root : Bool,
      (edges.map (fun e => A (σ e.1) (σ e.2) * A (σ e.1) root * A (σ e.2) root)).prod) =
      2 * ∑ σ : V → Bool, graphWeight (biased A) edges σ := by
  classical
  let flip : (V → Bool) ≃ (V → Bool) :=
    ⟨fun σ v => !(σ v),fun σ v => !(σ v),
      fun σ => funext (fun v => Bool.not_not (σ v)),
      fun σ => funext (fun v => Bool.not_not (σ v))⟩
  have he : (∑ σ : V → Bool, graphWeight (biased A) edges (fun v => !(σ v))) =
      ∑ σ : V → Bool, graphWeight (biased A) edges σ :=
    flip.sum_comp (graphWeight (biased A) edges)
  have hfalse (σ : V → Bool) :
      (edges.map (fun e => A (σ e.1) (σ e.2) * A (σ e.1) false * A (σ e.2) false)).prod =
        graphWeight (biased A) edges σ := rfl
  have htrue (σ : V → Bool) :
      (edges.map (fun e => A (σ e.1) (σ e.2) * A (σ e.1) true * A (σ e.2) true)).prod =
        graphWeight (biased A) edges (fun v => !(σ v)) := by
    simp only [triangle_true A hs hd,graphWeight]
  simp only [Fintype.sum_bool,hfalse,htrue,Finset.sum_add_distrib]
  rw [he]
  ring

end Ring

section Field
variable [Field K]

/-- The diagonal bias is forced by nonsingularity in the equal-diagonal case. -/
theorem biased_diagonal_ne (A : Bool → Bool → K)
    (hs : ∀ i j, A i j = A j i) (hd : A false false = A true true)
    (ha : A false false ≠ 0)
    (hdet : A false false * A true true ≠ A false true ^ 2) :
    biased A false false ≠ biased A true true := by
  intro h
  have he : A false false * (A false false * A false false) =
      A false false * (A false true * A false true) := by
    calc
      _ = biased A false false := by dsimp [biased]; ring
      _ = biased A true true := h
      _ = _ := by rw [biased,← hd,hs true false]; ring
  have hc := mul_left_cancel₀ ha he
  exact hdet (by simpa only [← hd,pow_two] using hc)

/-- Endpoint decoration preserves nonzero determinant; no hardness conclusion
is supplied in this algebraic lemma. -/
theorem biased_det_ne (A : Bool → Bool → K)
    (hs : ∀ i j, A i j = A j i) (ha : A false false ≠ 0) (hb : A false true ≠ 0)
    (hdet : A false false * A true true ≠ A false true ^ 2) :
    biased A false false * biased A true true ≠ biased A false true ^ 2 := by
  intro h
  have he : (A false false * A false true)^2 *
      (A false false * A true true - A false true^2) = 0 := by
    calc
      _ = biased A false false * biased A true true - biased A false true^2 := by
        simp only [biased,hs true false]
        ring
      _ = 0 := sub_eq_zero.mpr h
  exact hdet (sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left
    (pow_ne_zero _ (mul_ne_zero ha hb))))

theorem biased_positive (A : Bool → Bool → K) (ρ : K →+* ℝ)
    (hpos : ∀ i j, 0 < ρ (A i j)) : ∀ i j, 0 < ρ (biased A i j) := by
  intro i j
  simpa only [biased,map_mul] using mul_pos (mul_pos (hpos i j) (hpos i false)) (hpos j false)

end Field
end PositiveBinaryApex
end ComplexCSP
