import ComplexCSP.Structure.RowTypes
import PlanarHom.FixedFieldArithmeticMachines
import PlanarHom.ListMutationMachines
import PlanarHom.ConditionalMachines
import PlanarHom.MaterializedFieldListMachines

/-! # Canonical row labels from actual fixed-field arithmetic

The domain size is a fixed program constant; row entries are runtime data. The
first nonzero coordinate is found by a compiled finite sequence of exact field
equality tests. Zero rows produce none. Present rows are divided by their anchor.
-/
namespace ComplexCSP.ComplexityRowNormalization
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines

variable {K : Type} [Field K] [DecidableEq K] {d : ℕ}
abbrev Row (K : Type) (d : ℕ) := Fin d → K
abbrev Result (K : Type) (d : ℕ) := Option (Fin d × Row K d)

def divideAt (v : Row K d) (a : Fin d) : Row K d := fun j => v j / v a

def normalizeOn : List (Fin d) → Row K d → Result K d
  | [], _ => none
  | a::rest, v => if v a = 0 then normalizeOn rest v else some (a, divideAt v a)

def normalize (v : Row K d) : Result K d := normalizeOn (List.finRange d) v

theorem normalizeOn_none_iff (indices : List (Fin d)) (v : Row K d) :
    normalizeOn indices v = none ↔ ∀ a ∈ indices, v a = 0 := by
  induction indices with
  | nil => simp [normalizeOn]
  | cons a rest ih => by_cases ha : v a = 0 <;> simp [normalizeOn, ha, ih]

@[simp] theorem normalize_none_iff (v : Row K d) : normalize v = none ↔ v = 0 := by
  simp only [normalize, normalizeOn_none_iff, List.mem_finRange, forall_const]
  exact ⟨fun h => funext h, fun h => by simp [h]⟩

theorem normalizeOn_some_spec (indices : List (Fin d)) (v : Row K d)
    (a : Fin d) (w : Row K d) (h : normalizeOn indices v = some (a,w)) :
    a ∈ indices ∧ v a ≠ 0 ∧ w = divideAt v a := by
  induction indices with
  | nil => simp [normalizeOn] at h
  | cons b rest ih =>
    by_cases hb : v b = 0
    · have hs := ih (by simpa [normalizeOn, hb] using h)
      exact ⟨List.mem_cons_of_mem b hs.1, hs.2⟩
    · have he : (b,divideAt v b) = (a,w) := Option.some.inj (by simpa [normalizeOn,hb] using h)
      cases he
      exact ⟨List.mem_cons_self, hb, rfl⟩

theorem normalize_some_spec (v : Row K d) (a : Fin d) (w : Row K d)
    (h : normalize v = some (a,w)) :
    v a ≠ 0 ∧ w a = 1 ∧ (∀ j, v j = v a * w j) := by
  obtain ⟨_, ha, rfl⟩ := normalizeOn_some_spec (List.finRange d) v a w h
  refine ⟨ha, by simp [divideAt, ha], ?_⟩
  intro j
  change v j = v a * (v j / v a)
  rw [← mul_div_assoc, mul_comm (v a), mul_div_cancel_right₀ _ ha]

/-- Simultaneous nonzero scaling preserves the first anchor and every ratio. -/
theorem normalizeOn_scale (indices : List (Fin d)) (v : Row K d) (c : K) (hc : c ≠ 0) :
    normalizeOn indices (fun j => c*v j) = normalizeOn indices v := by
  induction indices with
  | nil => rfl
  | cons a rest ih =>
    by_cases ha : v a = 0
    · simp [normalizeOn, ha, ih]
    · simp only [normalizeOn, ha, mul_ne_zero hc ha, ↓reduceIte]
      congr 2
      funext j
      simp [divideAt, mul_div_mul_left, hc]

theorem normalize_scale (v : Row K d) (c : K) (hc : c ≠ 0) :
    normalize (fun j => c*v j) = normalize v := normalizeOn_scale _ v c hc

/-- The literal canonical labels identify exactly nonzero-proportional rows. -/
theorem normalize_eq_iff (u v : Row K d) (hu : u ≠ 0) :
    normalize u = normalize v ↔ ∃ c : K, c ≠ 0 ∧ ∀ j, u j = c * v j := by
  constructor
  · intro he
    cases hn : normalize u with
    | none => exact False.elim (hu ((normalize_none_iff u).mp hn))
    | some p =>
      rcases p with ⟨a,w⟩
      have hnv : normalize v = some (a,w) := he.symm.trans hn
      obtain ⟨hua, _, hur⟩ := normalize_some_spec u a w hn
      obtain ⟨hva, _, hvr⟩ := normalize_some_spec v a w hnv
      refine ⟨u a / v a, div_ne_zero hua hva, ?_⟩
      intro j
      rw [hur j, hvr j]
      field_simp
  · rintro ⟨c,hc,h⟩
    have hu' : u = fun j => c*v j := funext h
    rw [hu']
    exact normalize_scale v c hc

open scoped BigOperators

def rowSum (v : Row K d) : K := ∑ j, v j

/-- Exact summation factor, including cancellation to zero. -/
theorem normalize_sum (v : Row K d) (a : Fin d) (w : Row K d)
    (h : normalize v = some (a,w)) : rowSum v = v a * rowSum w := by
  obtain ⟨_, _, hr⟩ := normalize_some_spec v a w h
  unfold rowSum
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => hr j)

/-- Exact connection to the paper's nonzero row-equivalence relation. -/
theorem normalize_eq_nonzero_rows {X : Type} (G : X → Row K d) (x y : X) :
    normalize (G x) ≠ none ∧ normalize (G x) = normalize (G y) ↔
      RowTypes.NonzeroProportionalRows G x y := by
  constructor
  · rintro ⟨hn,he⟩
    have hx : G x ≠ 0 := fun hx => hn ((normalize_none_iff _).mpr hx)
    have hy : G y ≠ 0 := fun hy => hn (he.trans ((normalize_none_iff _).mpr hy))
    exact ⟨hx, hy, (normalize_eq_iff (G x) (G y) hx).mp he⟩
  · rintro ⟨hx,_hy,hp⟩
    exact ⟨fun hn => hx ((normalize_none_iff _).mp hn),
      (normalize_eq_iff (G x) (G y) hx).mpr hp⟩

section Machines
variable [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

noncomputable def rowEncoding (d : ℕ) : BitEncoding (Row K d) := (numberFieldEncoding basis).vector d

noncomputable def resultEncoding (d : ℕ) : BitEncoding (Result K d) :=
  ((BitEncoding.nat.prod (rowEncoding basis d)).list).retract
    (fun r => r.toList.map (fun p => (p.1.val,p.2)))
    (fun raw => raw.head?.bind (fun p => if h : p.1 < d then some (⟨p.1,h⟩,p.2) else none))
    (by intro r; cases r with
        | none => rfl
        | some p => rcases p with ⟨a,w⟩; simp [a.isLt])

omit [DecidableEq K] in
theorem fp_divideAt (a : Fin d) :
    FP (rowEncoding basis d) (rowEncoding basis d) (fun v => divideAt v a) := by
  apply FixedVectorMachines.fp_assemble (rowEncoding basis d) (numberFieldEncoding basis) d
  intro j
  exact ((FixedVectorMachines.fp_coordinate (numberFieldEncoding basis) d j).pair
    (FixedVectorMachines.fp_coordinate (numberFieldEncoding basis) d a)).comp
      (FixedFieldArithmetic.fp_division basis)

omit [DecidableEq K] in
theorem fp_normalizeAt (a : Fin d) :
    FP (rowEncoding basis d) (resultEncoding basis d) (fun v => some (a,divideAt v a)) := by
  let pairCode := BitEncoding.nat.prod (rowEncoding basis d)
  have hv := (fp_const (rowEncoding basis d) BitEncoding.nat a.val).pair (fp_divideAt basis a)
  have hs := (hv.pair (fp_const (rowEncoding basis d) pairCode.list [])).comp
    (ListMutationMachines.fp_cons pairCode)
  exact hs.transportOutput (fun _ => rfl)

/-- Every equality test and division is the actual bit-costed fixed-field machine. -/
theorem fp_normalizeOn (indices : List (Fin d)) :
    FP (rowEncoding basis d) (resultEncoding basis d) (normalizeOn indices) := by
  induction indices with
  | nil => exact fp_const _ _ none
  | cons a rest ih =>
    have hc := FixedVectorMachines.fp_coordinate (numberFieldEncoding basis) d a
    have hz := (hc.pair (fp_const (rowEncoding basis d) (numberFieldEncoding basis) 0)).comp
      (FixedFieldArithmetic.fp_equality basis)
    exact hz.ite ih (fp_normalizeAt basis a)

theorem fp_normalize : FP (rowEncoding basis d) (resultEncoding basis d) normalize :=
  fp_normalizeOn basis (List.finRange d)

omit [DecidableEq K] in
theorem fp_rowSum : FP (rowEncoding basis d) (numberFieldEncoding basis) rowSum := by
  have hl : FP (rowEncoding basis d) (numberFieldEncoding basis).list
      (fun v : Row K d => List.ofFn v) := fp_code_view _ _ _ (fun _ => rfl)
  exact (hl.comp (MaterializedFieldListMachines.fp_sum basis)).congr
    (fun _ => List.sum_ofFn)

end Machines
end ComplexCSP.ComplexityRowNormalization
