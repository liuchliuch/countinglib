import Counting.CookLevin.Target
import PlanarHom.OccurrencePfaffianListPrimitives
import PlanarHom.ListPredicateMachines

/-! A genuine polynomial-time evaluator for arbitrary target data. -/
namespace Counting.CookLevin
open PlanarHom.Complexity PlanarHom.CountingCookLevin
open PlanarHom.Complexity.PairProjectionMachines PlanarHom.ArithmeticCircuitPrimitives
open PlanarHom.ListFlattenMachines Polynomial

abbrev boolListEncoding := BitEncoding.bool.list
abbrev norGateEncoding := BitEncoding.nat.prod BitEncoding.nat

/-- Existing bounded scans implement total lookup even for huge binary indices. -/
theorem fp_readBit : FP (boolListEncoding.prod BitEncoding.nat) BitEncoding.bool
    (fun p => readBit p.1 p.2) := PlanarHom.PfaffianList.fp_at BitEncoding.bool false

theorem fp_extension : FP (BitEncoding.bool.prod BitEncoding.bool) boolListEncoding
    (fun p => List.ofFn (PlanarHom.ParsimoniousNorOneInThree.extension p.1 p.2)) := by
  have hf (i : Fin 4) := fp_bool_gate
    (fun p => PlanarHom.ParsimoniousNorOneInThree.extension p.1 p.2 i)
  have h0 := hf 0
  have h1 := hf 1
  have h2 := hf 2
  have h3 := hf 3
  have hz := fp_const (BitEncoding.bool.prod BitEncoding.bool) boolListEncoding []
  have hc := PlanarHom.ListMutationMachines.fp_cons BitEncoding.bool
  have h := (h0.pair ((h1.pair ((h2.pair ((h3.pair hz).comp hc)).comp hc)).comp hc)).comp hc
  exact h.congr (fun p => by simp [List.ofFn_succ])

theorem fp_norStep : FP (boolListEncoding.prod norGateEncoding) boolListEncoding
    (fun p => norStep p.1 p.2) := by
  have hs := fp_fst boolListEncoding norGateEncoding
  have hg := fp_snd boolListEncoding norGateEncoding
  have hl := (hs.pair (hg.comp (fp_fst BitEncoding.nat BitEncoding.nat))).comp fp_readBit
  have hr := (hs.pair (hg.comp (fp_snd BitEncoding.nat BitEncoding.nat))).comp fp_readBit
  exact (hs.pair ((hl.pair hr).comp fp_extension)).comp
    (PlanarHom.ListMutationMachines.fp_append BitEncoding.bool)

theorem boolList_length_bound (xs : List Bool) :
    (boolListEncoding.encode xs).length ≤ 9 * xs.length + 1 := by
  have h := word_length_le_payload BitEncoding.bool xs
  have hp : payloadSize BitEncoding.bool xs = 3 * xs.length := by
    simp [payloadSize_eq, BitEncoding.bool]
    omega
  rw [hp] at h
  change (BitEncoding.bool.list.encode xs).length ≤ _
  omega

/-- Every prefix stores exactly four additional bits per executed gate. -/
theorem nor_prefix_size_bound (xs : List Bool) (gs : NorGates) (i : ℕ) :
    (boolListEncoding.encode ((gs.take i).foldl norStep xs)).length ≤
      (C 45 * X + 1).eval ((boolListEncoding.prod norGateEncoding.list).encode (xs, gs)).length := by
  have hx := BitEncoding.list_length_le BitEncoding.bool xs
  change xs.length ≤ (boolListEncoding.encode xs).length at hx
  have hg := BitEncoding.list_length_le norGateEncoding gs
  have ht : (gs.take i).length ≤ gs.length := by simp
  have hs := boolList_length_bound (runNor (gs.take i) xs)
  rw [runNor_length] at hs
  simp only [eval_add, eval_mul, eval_C, eval_X, eval_one, BitEncoding.prod_length]
  change (boolListEncoding.encode (runNor (gs.take i) xs)).length ≤ _
  omega

theorem fp_runNor : FP (boolListEncoding.prod norGateEncoding.list) boolListEncoding
    (fun p => runNor p.2 p.1) :=
  PlanarHom.ListFoldMachines.fp_foldl norGateEncoding boolListEncoding norStep fp_norStep
    (C 45 * X + 1) (fun xs gs i _ => nor_prefix_size_bound xs gs i)

/-- Target execution is polynomial in encoded target plus actual witness length. -/
theorem fp_eval : FP (Instance.encoding.prod boolListEncoding) BitEncoding.bool
    (fun p => p.1.eval p.2) := by
  have hc := fp_fst Instance.encoding boolListEncoding
  have hw := fp_snd Instance.encoding boolListEncoding
  have hd := hc.comp (fp_snd BitEncoding.unaryNat (norGateEncoding.list.prod BitEncoding.nat))
  have hg := hd.comp (fp_fst norGateEncoding.list BitEncoding.nat)
  have ho := hd.comp (fp_snd norGateEncoding.list BitEncoding.nat)
  have hs := (hw.pair (fp_const _ boolListEncoding [true,false,false,false])).comp
    (PlanarHom.ListMutationMachines.fp_append BitEncoding.bool)
  exact (((hs.pair hg).comp fp_runNor).pair ho).comp fp_readBit

end Counting.CookLevin
