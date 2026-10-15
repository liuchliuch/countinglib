import Paper2.Certificates.DihedralSupport.AtlasCounts

/-! The defining V/E vectors of Appendix A.1, before a choice of parity
frame. The eight coordinates are four oriented complement blocks. -/
namespace Paper2.Certificates.DihedralSupport.AtlasVectors
open AtlasCounts
set_option maxRecDepth 10000

abbrev Coordinate := Block × Bool

variable {K : Type*} [Field K]

def singleVector (ω : K) (p : Block) (r : Phase) : Coordinate → K :=
  fun x => if x.1 = p then ω ^ ((if x.2 then 2 else 1) * r.val) else 0

def vector (ω : K) : PointLabel → Coordinate → K
  | .inl (p,r) => singleVector ω p r
  | .inr (p,r,t) => singleVector ω p.1.1 r - singleVector ω p.1.2 t

theorem single_support (ω : K) (p : Block) (r : Phase) (x : Coordinate)
    (hx : singleVector ω p r x ≠ 0) : x.1 = p := by
  by_contra h
  simp [singleVector,h] at hx

theorem single_support_iff (ω : K) (hω : ω ≠ 0) (p : Block) (r : Phase)
    (x : Coordinate) : singleVector ω p r x ≠ 0 ↔ x.1 = p := by
  unfold singleVector
  by_cases h : x.1 = p
  · rw [ite_eq_left h]
    exact iff_of_true (pow_ne_zero _ hω) h
  · rw [ite_eq_right h]
    simp [h]

theorem twoBlock_support (ω : K) (p : Pair) (r t : Phase) (x : Coordinate)
    (hx : vector ω (twoBlock p r t) x ≠ 0) : x.1 = p.1.1 ∨ x.1 = p.1.2 := by
  by_contra h
  push Not at h
  simp [vector,twoBlock,singleVector,h.1,h.2] at hx

theorem twoBlock_support_iff (ω : K) (hω : ω ≠ 0) (p : Pair) (r t : Phase)
    (x : Coordinate) : vector ω (twoBlock p r t) x ≠ 0 ↔
      x.1 = p.1.1 ∨ x.1 = p.1.2 := by
  have hp : p.1.1 ≠ p.1.2 := ne_of_lt p.2
  change singleVector ω p.1.1 r x - singleVector ω p.1.2 t x ≠ 0 ↔ _
  unfold singleVector
  by_cases h : x.1 = p.1.1
  · have hq : x.1 ≠ p.1.2 := h ▸ hp
    rw [ite_eq_left h,ite_eq_right hq,sub_zero]
    exact iff_of_true (pow_ne_zero _ hω) (Or.inl h)
  · by_cases hq : x.1 = p.1.2
    · rw [ite_eq_right h,ite_eq_left hq,zero_sub]
      exact iff_of_true (neg_ne_zero.mpr (pow_ne_zero _ hω)) (Or.inr hq)
    · rw [ite_eq_right h,ite_eq_right hq]
      simp [h,hq]

/-- A literal support receipt, retaining both one-block and two-block points. -/
theorem support_receipt (ω : K) (hω : ω ≠ 0) (l : PointLabel) :
    ∃ S : Finset Coordinate, S.card ≤ 4 ∧
      ∀ x, vector ω l x ≠ 0 ↔ x ∈ S := by
  cases l with
  | inl l =>
    rcases l with ⟨p,r⟩
    refine ⟨{(p,false),(p,true)},by simp,?_⟩
    intro x
    rw [show vector ω (.inl (p,r)) = singleVector ω p r from rfl,
      single_support_iff ω hω]
    rcases x with ⟨q,b⟩
    cases b <;> simp
  | inr l =>
    rcases l with ⟨p,r,t⟩
    refine ⟨{(p.1.1,false),(p.1.1,true),(p.1.2,false),(p.1.2,true)},?_ ,?_⟩
    · exact (Finset.card_insert_le _ _).trans (by
        have h1 := Finset.card_insert_le (p.1.1,true) {(p.1.2,false),(p.1.2,true)}
        have h2 := Finset.card_insert_le (p.1.2,false) {(p.1.2,true)}
        simp only [Finset.card_singleton] at h2
        omega)
    · intro x
      rw [show .inr (p,r,t) = twoBlock p r t from rfl,twoBlock_support_iff ω hω]
      rcases x with ⟨q,b⟩
      cases b <;> simp

private theorem power_cube (ω : K) (hω : ω^3 = 1) (a : ℕ) : (ω^a)^3 = 1 := by
  rw [← pow_mul, Nat.mul_comm a 3, pow_mul,hω,one_pow]

private theorem negative_power_cube (ω : K) (hω : ω^3 = 1) (a : ℕ) :
    (-ω^a)^3 = -1 := by
  calc
    (-ω^a)^3 = -(ω^a)^3 := by ring
    _ = -1 := by rw [power_cube ω hω]

/-- Every complement block has the same cubed coefficient at its two
oriented words. This includes the one-block generalized-equality points. -/
theorem complement_cube (ω : K) (hω : ω^3 = 1) (l : PointLabel) (p : Block) :
    vector ω l (p,true)^3 = vector ω l (p,false)^3 := by
  cases l with
  | inl l =>
    rcases l with ⟨q,r⟩
    by_cases h : p = q
    · simp only [vector,singleVector,h,ite_true,Bool.false_eq_true,ite_false]
      exact (power_cube ω hω _).trans (power_cube ω hω _).symm
    · simp [vector,singleVector,h]
  | inr l =>
    rcases l with ⟨q,r,t⟩
    have hq : q.1.1 ≠ q.1.2 := ne_of_lt q.2
    by_cases h : p = q.1.1
    · have hh : p ≠ q.1.2 := h ▸ hq
      dsimp only [vector,Pi.sub_apply,singleVector]
      rw [ite_eq_left h,ite_eq_right hh,sub_zero,ite_eq_left h,ite_eq_right hh,sub_zero]
      exact (power_cube ω hω _).trans (power_cube ω hω _).symm
    · by_cases hh : p = q.1.2
      · dsimp only [vector,Pi.sub_apply,singleVector]
        rw [ite_eq_right h,ite_eq_left hh,zero_sub,ite_eq_right h,ite_eq_left hh,zero_sub]
        rw [negative_power_cube ω hω,negative_power_cube ω hω]
      · simp [vector,singleVector,h,hh]

theorem complement_support (ω : K) (hω : ω^3 = 1) (l : PointLabel) (p : Block) :
    vector ω l (p,true) ≠ 0 ↔ vector ω l (p,false) ≠ 0 := by
  have h := complement_cube ω hω l p
  have hh : vector ω l (p,true)^3 ≠ 0 ↔ vector ω l (p,false)^3 ≠ 0 := by rw [h]
  simpa using hh

end Paper2.Certificates.DihedralSupport.AtlasVectors
