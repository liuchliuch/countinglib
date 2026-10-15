import ComplexCSP.Complexity.CountRecovery
import PlanarHom.ProductRepresentativeSemantics
import Mathlib.Analysis.Complex.Basic

/-! # Exact recovery of fixed-alphabet product replacements -/
namespace ComplexCSP.ComplexityProductReplacement
open scoped BigOperators
open PlanarHom
variable {K : Type} [Field K] [DecidableEq K] {t : ℕ}

private theorem sum_nonzero {S : Type} [Fintype S] (w f : S → K)
    (hf : ∀ a, w a = 0 → f a = 0) :
    (∑ a, f a) = ∑ a : {a // w a ≠ 0}, f a.val := by
  classical
  have hs := Fintype.sum_subtype_add_sum_subtype (fun a => w a ≠ 0) f
  have hz : (∑ a : {a // ¬w a ≠ 0}, f a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    exact hf a.val (not_ne_iff.mp a.property)
  simpa only [hz,add_zero] using hs.symm

/-- The source and target products are computed from actual words, not from a
supplied product-class oracle. Collisions and zero entries are handled exactly. -/
theorem recover_word_products {S : Type} [Fintype S] (A B : Fin t → K)
    (hcompat : ProductCompatibility.Compatible A B)
    (hzero : ∀ i, A i = 0 → B i = 0)
    (word : S → List (Fin t)) (m : ℕ) (hlen : ∀ a, (word a).length = m) :
    MaterializedLagrangeRecoveryMachines.recover
      (ExponentProductTables.representatives A B m,
        List.ofFn (fun h : Fin (ExponentProductTables.representatives A B m).length =>
          ∑ a, ((word a).map A).prod ^ (h.val+1))) =
      ∑ a, ((word a).map B).prod := by
  classical
  let w := fun a => ((word a).map A).prod
  let v := fun a => ((word a).map B).prod
  let μ := ExponentProductTables.sourceNode A B m
  let η := ExponentProductTables.targetNode A B m
  have hz : ∀ a, w a = 0 → v a = 0 := by
    intro a ha
    obtain ⟨i,hi,hiz⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp ha)
    exact List.prod_eq_zero_iff.mpr (List.mem_map.mpr ⟨i,hi,hzero i hiz⟩)
  have hex : ∀ a : {a // w a ≠ 0}, ∃ i, μ i = w a.val ∧ η i = v a.val := by
    intro a
    have hf := WordFrequencies.frequencies_mem_weak (word a.val)
    rw [hlen] at hf
    have he := ExponentProductSemantics.value_frequencies A (word a.val)
    have he' := ExponentProductSemantics.value_frequencies B (word a.val)
    obtain ⟨i,hi,hi'⟩ := ExponentProductTables.exists_node_for_weak A B hcompat
      (WordFrequencies.frequencies (word a.val)) hf (by rw [he]; exact a.property)
    exact ⟨i,hi.trans he,hi'.trans he'⟩
  choose cls hμ hη using hex
  rw [MaterializedLagrangeRecoveryMachines.recover_computed_table]
  have hq : (fun h : Fin (ExponentProductTables.representatives A B m).length =>
      ∑ a, w a^(h.val+1)) =
      (fun h => ∑ a : {a // w a ≠ 0}, (1 : K) * μ (cls a)^(h.val+1)) := by
    funext h
    rw [sum_nonzero w _ (fun a ha => by simp [ha])]
    simp only [one_mul,hμ]
  change LagrangeRecovery.evaluateReplacement μ η (fun h => ∑ a, w a^(h.val+1)) = ∑ a,v a
  rw [hq,LagrangeRecovery.evaluateReplacement_grouped_queries cls (fun _ => 1) μ η
    (ExponentProductTables.sourceNode_injective A B m)
    (ExponentProductTables.sourceNode_nonzero A B m)]
  rw [sum_nonzero w v hz]
  simp only [mul_one,hη]

omit [DecidableEq K] in
/-- Absolute value is an actual product-collision invariant under the embedding. -/
theorem compatible_of_absolute_embedding {I : Type} (σ : K →+* ℂ) (A B : I → K)
    (habs : ∀ i, σ (B i) = (‖σ (A i)‖ : ℂ)) : ProductCompatibility.Compatible A B := by
  intro xs ys _ _ _ h
  apply σ.injective
  have hword (zs : List I) : σ ((zs.map B).prod) = (‖σ ((zs.map A).prod)‖ : ℂ) := by
    induction zs with
    | nil => simp
    | cons i is ih => simp [habs,ih]
  rw [hword xs,hword ys,h]

omit [DecidableEq K] in
theorem zeros_of_absolute_embedding {I : Type} (σ : K →+* ℂ) (A B : I → K)
    (habs : ∀ i, σ (B i) = (‖σ (A i)‖ : ℂ)) : ∀ i, A i = 0 → B i = 0 := by
  intro i hi
  apply σ.injective
  simp [habs,hi]

end ComplexCSP.ComplexityProductReplacement
