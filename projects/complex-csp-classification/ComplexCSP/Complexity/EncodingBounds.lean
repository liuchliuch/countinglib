import PlanarHom.ListFlattenMachines

/-! # Elementary literal-codeword bounds for materialized algorithms -/
namespace ComplexCSP.ComplexityEncodingBounds
open PlanarHom PlanarHom.Complexity PlanarHom.ListFlattenMachines
variable {A : Type}

theorem encoded_mem_le (e : BitEncoding A) {a : A} {xs : List A} (ha : a ∈ xs) :
    (e.encode a).length ≤ (e.list.encode xs).length := by
  have hm := ListMapMachines.mem_le_sum_map (fun x => (e.encode x).length) ha
  have hp := payloadSize_le_word e xs
  rw [payloadSize_eq] at hp
  omega

theorem encoded_list_le (e : BitEncoding A) (xs : List A) (B : ℕ)
    (hB : ∀ a ∈ xs, (e.encode a).length ≤ B) :
    (e.list.encode xs).length ≤ (6*B+3)*xs.length+1 := by
  have hs := ListMapMachines.sum_map_le_mul (fun a => (e.encode a).length) xs B hB
  have hp := word_length_le_payload e xs
  rw [payloadSize_eq] at hp
  nlinarith

end ComplexCSP.ComplexityEncodingBounds
