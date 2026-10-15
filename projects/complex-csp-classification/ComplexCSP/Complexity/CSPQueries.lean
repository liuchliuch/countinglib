import ComplexCSP.Complexity.CSPNodes
import PlanarHom.ListReverseMachines

/-! Actual FP repetition-query batches on literal arbitrary-arity CSP codes. -/
namespace ComplexCSP.ComplexityCSPQueries
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityCSPCode

/-- Zero followed by every positive repetition up to the supplied candidate count. -/
def queries (g : Code) (N : ℕ) : List Code :=
  repeatCode g 0 :: (List.range N).map (fun i => repeatCode g (i + 1))

@[simp] theorem queries_length (g : Code) (N : ℕ) : (queries g N).length = N + 1 := by
  simp [queries]

theorem queries_valid {D K : Type} {s : ℕ} (L : Language D K (Fin s))
    (g : Code) (hg : Valid L g) (N : ℕ) : ∀ q ∈ queries g N, Valid L q := by
  intro q hq
  rcases List.mem_cons.mp hq with hq | hq
  · subst q
    exact repeat_valid L g hg 0
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hq
    exact repeat_valid L g hg _

/-- Generic ascending positive batch, compiled with unary-capped exponents. -/
theorem fp_positiveQueries : FP (BitEncoding.unaryNat.prod encoding) encoding.list
    (fun p : ℕ × Code => (List.range p.1).map (fun i => repeatCode p.2 (i + 1))) := by
  let ei := BitEncoding.unaryNat.prod encoding
  have hc := fp_fst ei BitEncoding.nat
  have hi := fp_snd ei BitEncoding.nat
  have hn := hc.comp (fp_fst BitEncoding.unaryNat encoding)
  have hg := hc.comp (fp_snd BitEncoding.unaryNat encoding)
  have hs := hi.comp BinaryArithmetic.fp_successor
  have he := (hn.pair hs).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    BitEncoding.unaryNat (fun p => min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
  have hb := (he.pair hg).comp fp_repeat
  have hm := ListContextMachines.fp_mapWithContext ei BitEncoding.nat encoding
    (fun p => repeatCode p.1.2 (min p.1.1 (p.2 + 1))) hb
  have hrange := (UnaryRangeMachines.fp_range.comp
    (ListReverseMachines.fp_reverse BitEncoding.nat)).congr
      (fun n => List.reverse_reverse (List.range n))
  have hr := (fp_fst BitEncoding.unaryNat encoding).comp hrange
  apply (((fp_id ei).pair hr).comp hm).congr
  intro p
  apply List.map_congr_left
  intro i hi
  change repeatCode p.2 (min p.1 (i + 1)) = repeatCode p.2 (i + 1)
  rw [min_eq_right (Nat.succ_le_of_lt (List.mem_range.mp hi))]

/-- The complete batch includes the zero query, so it handles zero weights and
languages whose every assignment has zero product. -/
theorem fp_queries : FP (BitEncoding.unaryNat.prod encoding) encoding.list
    (fun p : ℕ × Code => queries p.2 p.1) := by
  have hg := fp_snd BitEncoding.unaryNat encoding
  have hzero := ((fp_const (BitEncoding.unaryNat.prod encoding) BitEncoding.unaryNat 0).pair hg).comp fp_repeat
  exact (hzero.pair fp_positiveQueries).comp (ListMutationMachines.fp_cons encoding)

end ComplexCSP.ComplexityCSPQueries
