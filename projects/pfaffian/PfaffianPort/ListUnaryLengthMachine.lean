import PfaffianPort.ListCodecMachines
import PfaffianPort.BoundedUnaryMachines
import PfaffianPort.ArithmeticCircuitPrimitives

/-! Explicit unary list lengths, bounded by their materialized input codewords. -/
namespace PfaffianPort.ListUnaryLengthMachine
open PfaffianPort.Complexity

theorem fp_length {α : Type} (e : BitEncoding α) :
    FP e.list BitEncoding.unaryNat List.length:=by
  have hN : FP e.list BitEncoding.unaryNat (fun xs=>(e.list.encode xs).length):=
    ⟨PfaffianPort.InputLengthMachine.computer e.list⟩
  have hn:=PfaffianPort.Complexity.ListCodecMachines.fp_length e
  have h:=((hN.pair hn).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    BitEncoding.unaryNat (fun p=>min p.1 p.2) from ⟨PfaffianPort.BoundedUnaryMachines.computer⟩))
  exact h.congr (fun xs=>min_eq_right (BitEncoding.list_length_le e xs))

end PfaffianPort.ListUnaryLengthMachine
