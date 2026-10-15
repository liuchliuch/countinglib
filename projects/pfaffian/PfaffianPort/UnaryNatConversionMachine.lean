import PfaffianPort.RestrictedIterationMachine
import PfaffianPort.GraphParallelCode

/-! Actual unary-to-canonical-binary conversion by bounded successor iteration. -/
namespace PfaffianPort.UnaryNatConversionMachine
open Turing Polynomial PfaffianPort.Complexity PfaffianPort.BinaryArithmetic

private theorem successor_iterate (n : ℕ) : (fun x : ℕ=>x+1)^[n] 0=n:=by
  induction n with
  | zero=>rfl
  | succ n ih=>simp [Function.iterate_succ_apply',ih]

noncomputable def computer :
    TM2ComputableInPolyTime BitEncoding.unaryNat.encode BitEncoding.nat.encode id:=by
  let c:=PfaffianPort.BoundedIterationMachine.fromSeedComputer BitEncoding.nat (fun x=>x+1) 0
    successorComputable X (fun n i hi=>by
      simpa only [successor_iterate,Polynomial.eval_X] using (encodeNat_length_le i).trans hi)
  have he : (fun n=>(fun x : ℕ=>x+1)^[n] 0)=id:=funext successor_iterate
  rw [he] at c
  exact c

theorem fp_conversion : FP BitEncoding.unaryNat BitEncoding.nat id:=⟨computer⟩

end PfaffianPort.UnaryNatConversionMachine
