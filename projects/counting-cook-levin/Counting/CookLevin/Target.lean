import PlanarHom.CountingCookLevinNorCircuit
import Counting.Foundation.Witness

/-!
# A source-independent encoded NOR counting target

The instance stores only an explicit witness arity, a materialized gate list,
and an output address. Addresses are binary; the arity is unary. Every gate
appends the original four deterministic NOR-gadget registers. No auxiliary
register is a guessed witness bit. Out-of-range reads return false, including
forward references; an out-of-range final output therefore rejects.
-/
namespace Counting.CookLevin
open PlanarHom.Complexity PlanarHom.CountingCookLevin

/-- `(witness arity, (materialized gates, output address))`. -/
abbrev Instance := ℕ × (NorGates × ℕ)

namespace Instance

def arity (c : Instance) : ℕ := c.1
def gates (c : Instance) : NorGates := c.2.1
def output (c : Instance) : ℕ := c.2.2

/-- Unary arity prevents exponentially many hidden input wires. Gate references
and the output address use actual binary integers and framed list metadata. -/
def encoding : BitEncoding Instance :=
  BitEncoding.unaryNat.prod
    (((BitEncoding.nat.prod BitEncoding.nat).list).prod BitEncoding.nat)

/-- The only initial constants are fixed, with no multiplicity of assignments. -/
def initial (w : List Bool) : List Bool := w ++ [true, false, false, false]

/-- Deterministic execution depends only on the target and supplied witness. -/
def eval (c : Instance) (w : List Bool) : Bool :=
  readBit (runNor c.gates (initial w)) c.output

/-- Once the target fields and witness are fixed, no source machine/input can
change evaluation; the arity is used solely by the independent counting domain. -/
theorem eval_eq_of_program_eq (c d : Instance) (hg : c.gates = d.gates)
    (ho : c.output = d.output) (w : List Bool) : c.eval w = d.eval w := by
  simp only [eval, hg, ho]

/-- Count exactly `arity` independent bits; no gate-output bits are free. -/
def count (c : Instance) : ℕ := Counting.Foundation.witnessCount c.arity c.eval

theorem arity_le_encoded_length (c : Instance) :
    c.arity ≤ (encoding.encode c).length := by
  simp only [arity, encoding, BitEncoding.prod_length, BitEncoding.unaryNat_length]
  omega

/-- Even on malformed addresses, the actual store size is explicit and finite. -/
theorem store_length (c : Instance) (w : List Bool) :
    (runNor c.gates (initial w)).length = w.length + 4 + 4 * c.gates.length := by
  simp [initial]

theorem eval_out_of_range (c : Instance) (w : List Bool)
    (h : w.length + 4 + 4 * c.gates.length ≤ c.output) : c.eval w = false := by
  have h' : (runNor c.gates (initial w)).length ≤ c.output := by rwa [store_length]
  simp [eval, readBit, List.getElem?_eq_none h']

theorem count_le (c : Instance) : c.count ≤ 2 ^ c.arity :=
  Counting.Foundation.witnessCount_le c.arity c.eval

end Instance
end Counting.CookLevin
