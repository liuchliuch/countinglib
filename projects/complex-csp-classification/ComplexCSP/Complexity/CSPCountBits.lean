import ComplexCSP.Complexity.CSPCode
import PlanarHom.ZeroOneVerifierMachines
import PlanarHom.TotalListCodecParser

/-! # Total raw CSP parsing and actual polynomial-time bit equality

The target field word is compared with the canonical encoded computed product.
Only the fixed field's own coordinate words are promised as target inputs.
-/
namespace ComplexCSP
namespace ComplexityCSPCountBits
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives PlanarHom.ZeroOneSharpPMembership

def bitsEqual (p : Bits × Bits) : Bool := decide (p.1 = p.2)

theorem bits_eq_iff (xs ys : Bits) : xs = ys ↔ xs.length = ys.length ∧
    ∀ i, i < xs.length → getBit xs i = getBit ys i := by
  constructor
  · rintro rfl; exact ⟨rfl,fun _ _ => rfl⟩
  · rintro ⟨hlen,h⟩
    apply List.ext_getElem hlen
    intro i hi hj
    have hh := h i hi
    simpa [getBit,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj] using hh

theorem fp_bitsEqual : FP (BitEncoding.bits.prod BitEncoding.bits) BitEncoding.bool bitsEqual := by
  let e := BitEncoding.bits.prod BitEncoding.bits
  have hx := fp_fst BitEncoding.bits BitEncoding.bits
  have hy := fp_snd BitEncoding.bits BitEncoding.bits
  have hlen : FP BitEncoding.bits BitEncoding.unaryNat (fun w : Bits => w.length) :=
    ⟨InputLengthMachine.computer BitEncoding.bits⟩
  have hnx := hx.comp hlen
  have hny := hy.comp hlen
  have hsame := ((hnx.comp UnaryNatConversionMachine.fp_conversion).pair
    (hny.comp UnaryNatConversionMachine.fp_conversion)).comp NatListSumMachines.fp_equal
  have hc := fp_fst e BitEncoding.nat
  have hi := fp_snd e BitEncoding.nat
  have hl := ((hc.comp hx).pair hi).comp fp_getBit
  have hr := ((hc.comp hy).pair hi).comp fp_getBit
  have hb := (hl.pair hr).comp (fp_bool_gate (fun p => decide (p.1 = p.2)))
  have ha := ((fp_id e).pair (hnx.comp fp_range)).comp (fp_allContext e BitEncoding.nat _ hb)
  exact ((hsame.pair ha).comp (fp_bool_gate (fun p => p.1 && p.2))).congr (fun p => by
    apply Bool.eq_iff_iff.mpr
    simp only [Function.comp_apply,Function.comp_def,id_eq]
    simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,List.mem_range,bitsEqual]
    exact (bits_eq_iff p.1 p.2).symm)

end ComplexityCSPCountBits

namespace ComplexityCSPCode
open PlanarHom.Complexity

noncomputable def totalParser : BitEncoding.TotalParser encoding :=
  ((BitEncoding.TotalParser.unaryNat).prod
    (BitEncoding.TotalParser.nat.prod BitEncoding.TotalParser.nat.list).list).retract
      (fun g : Code => (g.vertices,g.constraints)) (fun p => ⟨p.1,p.2⟩)
      (fun g => by cases g; rfl) (fun p => by cases p; rfl)

theorem fp_totalParser : FP BitEncoding.bits (BitEncoding.bool.prod encoding) totalParser.run :=
  totalParser.fp

theorem totalParser_encode (g : Code) : totalParser.run (encoding.encode g) = (true,g) := by
  have h := totalParser.correct (encoding.encode g)
  rw [encoding.decode_encode] at h
  cases hf : (totalParser.run (encoding.encode g)).1
  · simp [hf] at h
  · have hp : (totalParser.run (encoding.encode g)).2 = g := by simpa [hf] using h.symm
    exact Prod.ext hf hp

end ComplexityCSPCode
end ComplexCSP
