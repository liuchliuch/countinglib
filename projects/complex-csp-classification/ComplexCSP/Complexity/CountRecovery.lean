import ComplexCSP.Complexity.WeightProfiles
import PlanarHom.MaterializedLagrangeRecoveryMachines

/-!
# Effective multiplicity recovery from partition moments

The program is literal materialized shifted Lagrange recovery. Zero-weight
assignments are recovered by subtracting the nonzero count from the known total.
The polynomial-time postprocessor below uses the existing genuine fixed-field
bit machines. CSPCountReduction composes them into the full oracle reduction.
-/
namespace ComplexCSP.ComplexityCountRecovery
open scoped BigOperators
open PlanarHom

variable {K : Type} [Field K] [DecidableEq K]

/-- Recover a specified multiplicity; the total is supplied by the explicit
zeroth-moment query (the empty-constraint instance on the same variables). -/
def recover (total : K) (nodes answers : List K) (z : K) : K :=
  if z = 0 then
    total - MaterializedLagrangeRecoveryMachines.recover
      (nodes.map (fun μ => (μ, 1)), answers)
  else
    MaterializedLagrangeRecoveryMachines.recover
      (nodes.map (fun μ => (μ, if μ = z then 1 else 0)), answers)

/-- Natural multiplicity of one weight in an arbitrary finite assignment family. -/
def count {A : Type} [Fintype A] (w : A → K) (z : K) : ℕ :=
  (Finset.univ.filter (fun a => w a = z)).card

theorem sum_grouped {A : Type} [Fintype A] {n : ℕ}
    (w : A → K) (μ : Fin n → K) (hμ : Function.Injective μ)
    (hcover : ∀ a, w a ≠ 0 → ∃ i, μ i = w a)
    (f : K → K) (hf : f 0 = 0) :
    (∑ i, (count w (μ i) : K) * f (μ i)) = ∑ a, f (w a) := by
  classical
  let S := (Finset.univ : Finset A).filter (fun a => w a ≠ 0)
  let T := (Finset.univ : Finset (Fin n)).image μ
  have hc : ∀ a ∈ S, w a ∈ T := by
    intro a ha
    obtain ⟨i, hi⟩ := hcover a (Finset.mem_filter.mp ha).2
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩
  have hsum := Finset.sum_fiberwise_eq_sum_filter
    (Finset.univ : Finset A) T w (fun a => f (w a))
  have hout : (∑ a ∈ Finset.univ.filter (fun a => w a ∈ T), f (w a)) =
      ∑ a, f (w a) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro a _ ha
    have hz : w a = 0 := by
      by_contra hn
      obtain ⟨i, hi⟩ := hcover a hn
      exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩⟩)
    rw [hz, hf]
  rw [hout] at hsum
  rw [← hsum]
  dsimp [T]
  rw [Finset.sum_image (fun i _ j _ hij => hμ hij)]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (∑ a ∈ Finset.univ.filter (fun a => w a = μ i), f (w a)) =
      ∑ _a ∈ Finset.univ.filter (fun a => w a = μ i), f (μ i) from
    Finset.sum_congr rfl (fun a ha => congrArg f (Finset.mem_filter.mp ha).2)]
  simp [count, nsmul_eq_mul]

/-- The postprocessor recovers every requested count, including zero and values
outside the candidate list. Correctness has no positivity/sign assumptions. -/
theorem recover_moments {A : Type} [Fintype A] {n : ℕ}
    (w : A → K) (μ : Fin n → K) (hμ : Function.Injective μ)
    (hzero : ∀ i, μ i ≠ 0)
    (hcover : ∀ a, w a ≠ 0 → ∃ i, μ i = w a) (z : K) :
    recover (Fintype.card A : K) (List.ofFn μ)
      (List.ofFn (fun h : Fin n => ∑ a, w a ^ (h.val + 1))) z = count w z := by
  classical
  have hm : (fun h : Fin n => ∑ a, w a ^ (h.val + 1)) =
      Interpolation.queryValues μ (fun i => (count w (μ i) : K)) := by
    funext h
    symm
    exact sum_grouped w μ hμ hcover (fun v => v ^ (h.val + 1)) (by simp)
  have hr (η : Fin n → K) :
      MaterializedLagrangeRecoveryMachines.recover
        (List.ofFn (fun i => (μ i, η i)),
          List.ofFn (fun h : Fin n => ∑ a, w a ^ (h.val + 1))) =
        ∑ i, η i * (count w (μ i) : K) := by
    rw [hm]
    exact MaterializedLagrangeRecoveryMachines.recover_queryValues μ η _ hμ hzero
  unfold recover
  split_ifs with hz
  · subst z
    simp only [List.map_ofFn, Function.comp_def]
    rw [hr]
    have hs := sum_grouped w μ hμ hcover (fun v => if v = 0 then 0 else 1) (by simp)
    simp only [hzero, ↓reduceIte, mul_one] at hs
    simp only [one_mul]
    rw [hs]
    have hc : (count w 0 : K) = ∑ a : A, if w a = 0 then 1 else 0 := by
      simp [count]
    rw [hc]
    have htotal : (Fintype.card A : K) =
        (∑ a : A, if w a = 0 then 0 else 1) + ∑ a : A, if w a = 0 then 1 else 0 := by
      rw [← Finset.sum_add_distrib]
      simp only [ite_add_ite, zero_add, add_zero, ite_self, Finset.sum_const,
        Finset.card_univ, nsmul_one]
    exact sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using htotal)
  · simp only [List.map_ofFn, Function.comp_def]
    rw [hr]
    have hs := sum_grouped w μ hμ hcover (fun v => if v = z then 1 else 0)
      (by simp [Ne.symm hz])
    have he : (∑ i, (if μ i = z then 1 else 0) * (count w (μ i) : K)) =
        ∑ a : A, if w a = z then 1 else 0 := by
      simpa only [mul_comm] using hs
    rw [he]
    simp [count]

section Machines
open PlanarHom.Complexity PlanarHom.ArithmeticCircuitPrimitives
  PlanarHom.Complexity.PairProjectionMachines
variable [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

abbrev Input (K : Type) := K × (List K × (List K × K))
noncomputable def inputEncoding : BitEncoding (Input K) :=
  let e := numberFieldEncoding basis
  e.prod (e.list.prod (e.list.prod e))

def recoverInput (p : Input K) : K := recover p.1 p.2.1 p.2.2.1 p.2.2.2

/-- The entire field-valued multiplicity postprocessor is a real FP composition
on literal input words. No moment correctness or growth premise is needed. -/
theorem fp_recover : FP (inputEncoding basis) (numberFieldEncoding basis) recoverInput := by
  let e := numberFieldEncoding basis
  let ei := inputEncoding basis
  have ht := fp_fst e (e.list.prod (e.list.prod e))
  have hn := (fp_snd e (e.list.prod (e.list.prod e))).comp (fp_fst e.list (e.list.prod e))
  have ha := ((fp_snd e (e.list.prod (e.list.prod e))).comp
    (fp_snd e.list (e.list.prod e))).comp (fp_fst e.list e)
  have hz := ((fp_snd e (e.list.prod (e.list.prod e))).comp
    (fp_snd e.list (e.list.prod e))).comp (fp_snd e.list e)
  have hrowOne : FP e (e.prod e) (fun μ : K => (μ, 1)) :=
    (fp_id e).pair (fp_const e e 1)
  have hones := hn.comp (ListMapMachines.fp_map e (e.prod e) _ hrowOne)
  have hone := (hones.pair ha).comp (MaterializedLagrangeRecoveryMachines.fp_recover basis)
  have heq : FP (e.prod e) BitEncoding.bool (fun p : K × K => decide (p.2 = p.1)) :=
    ((fp_snd e e).pair (fp_fst e e)).comp (FixedFieldArithmetic.fp_equality basis)
  have hbit := heq.comp (fp_bool_unary e (fun b => if b then (1 : K) else 0))
  have hrow : FP (e.prod e) (e.prod e)
      (fun p : K × K => (p.2, if p.2 = p.1 then 1 else 0)) := by
    exact ((fp_snd e e).pair hbit).congr (fun _ => by simp)
  have htargets := (hz.pair hn).comp
    (ListContextMachines.fp_mapWithContext e e (e.prod e) _ hrow)
  have htarget := (htargets.pair ha).comp (MaterializedLagrangeRecoveryMachines.fp_recover basis)
  have hzero := ((hz.pair (fp_const ei e 0)).comp
    (FixedFieldArithmetic.fp_equality basis)).comp
      (fp_bool_unary e (fun b => if b then (1 : K) else 0))
  have hdiff := (ht.pair hone).comp (FixedFieldArithmetic.fp_subtraction basis)
  have hleft := (hzero.pair hdiff).comp (FixedFieldArithmetic.fp_multiplication basis)
  have hnot := ((fp_const ei e 1).pair hzero).comp (FixedFieldArithmetic.fp_subtraction basis)
  have hright := (hnot.pair htarget).comp (FixedFieldArithmetic.fp_multiplication basis)
  exact ((hleft.pair hright).comp (FixedFieldArithmetic.fp_addition basis)).congr
    (fun p => by
      dsimp only [recoverInput, recover]
      by_cases h : p.2.2.2 = 0 <;> simp [h])

end Machines
end ComplexCSP.ComplexityCountRecovery
