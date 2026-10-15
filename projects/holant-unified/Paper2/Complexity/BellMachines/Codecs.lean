/- Extracted concrete finite-machine foundation; see docs/BELL_LIST_MACHINES_REUSE.json. -/
import Paper2.Complexity.FramedEncoding
namespace Paper2.Complexity.BellMachines.Codecs
open Computability Paper2.Algebraic
/-- A framed index determines the dependent payload's type and decoder. -/
def sigmaEncoding {α : Type} {β : α → Type} (ea : Encoding α Bool)
    (eb : ∀ a, Encoding (β a) Bool) : Encoding (Sigma β) Bool where
  encode p := frame (ea.encode p.1) ++ (eb p.1).encode p.2
  decode bits := do
    let (first, rest) ← unframe bits
    let a ← ea.decode first
    let value ← (eb a).decode rest
    pure ⟨a, value⟩
  decode_encode p := by cases p; simp

@[simp] theorem sigmaEncoding_length {α : Type} {β : α → Type}
    (ea : Encoding α Bool) (eb : ∀ a, Encoding (β a) Bool) (p : Sigma β) :
    ((sigmaEncoding ea eb).encode p).length =
      2 * (ea.encode p.1).length + 1 + ((eb p.1).encode p.2).length := by
  simp [sigmaEncoding]


/-- Physical unary bounded positions, independent of graph/signature semantics. -/
def unaryPortEncoding (n : ℕ) : Encoding (Fin n) Bool where
  encode i := List.replicate i.val true
  decode bits := if h : bits.all id = true ∧ bits.length < n then some ⟨bits.length, h.2⟩ else none
  decode_encode i := by simp [i.isLt]
end Paper2.Complexity.BellMachines.Codecs
