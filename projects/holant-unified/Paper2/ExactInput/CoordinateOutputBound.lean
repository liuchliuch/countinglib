import Paper2.ExactInput.FixedFieldBridge
import Paper2.ExactInput.Bounds.EncodedHolantOutputSize

/-! Fixed-family polynomial rational-coordinate output bounds for the original
literal graph input. These prove mathematical bit lengths, not evaluation time
and not yet public minimal-polynomial/complex-isolation output conversion. -/
namespace Paper2.ExactInput
open Paper2.Tractable Paper2.Algebraic Paper2.Complexity Paper2.Problem

noncomputable def exactTables (w : Wiring) (L : Language) :
    ExactSignatureTables (Module.finrank ℚ L.coefficientField) L.count 1 L.arity where
  vertex i x := L.fieldPresentation.basis.equivFun (L.fieldSignature i x)
  edge _ a b := L.fieldPresentation.basis.equivFun (fieldKernel L w a b)

@[simp] theorem exactTables_vertex_decode (w : Wiring) (L : Language)
    (i : Fin L.count) (x : Fin (L.arity i.val) → Bool) :
    L.fieldPresentation.decode ((exactTables w L).vertex i x) = L.fieldSignature i x :=
  L.fieldPresentation.basis.equivFun.symm_apply_apply _

@[simp] theorem exactTables_edge_decode (w : Wiring) (L : Language)
    (i : Fin 1) (a b : Bool) :
    L.fieldPresentation.decode ((exactTables w L).edge i a b) = fieldKernel L w a b :=
  L.fieldPresentation.basis.equivFun.symm_apply_apply _

theorem exactTables_evaluate (w : Wiring) (L : Language) (G : Instance L) :
    (exactTables w L).evaluate L.fieldPresentation G = (fieldNetwork w L G).denote Fin.elim0 := by
  rw [ExactSignatureTables.evaluate_eq_decoded]
  simp only [exactTables_vertex_decode, exactTables_edge_decode]
  rfl

/-- Explicit affine polynomial; all constants depend only on the original fixed
language/number field, and the variable is the actual framed graph input length. -/
noncomputable def coordinateOutputPolynomial (w : Wiring) (L : Language) : Polynomial ℕ :=
  (exactTables w L).outputPolynomial L.fieldPresentation

/-- Exact rational-coordinate bits for actual Holant answers have polynomial length. -/
theorem coordinate_output_length_le (w : Wiring) (L : Language) (G : Instance L) :
    ((vectorEncoding (Module.finrank ℚ L.coefficientField)).encode (outputCoordinates w L G)).length ≤
      (coordinateOutputPolynomial w L).eval ((inputEncoding L).encode G).length := by
  have h := (exactTables w L).output_length_le L.fieldPresentation G
  rw [exactTables_evaluate] at h
  exact h

noncomputable def coordinateOutputBound (w : Wiring) (L : Language) :
    PolynomialOutputBound (inputEncoding L)
      (vectorEncoding (Module.finrank ℚ L.coefficientField)) (outputCoordinates w L) where
  bound := coordinateOutputPolynomial w L
  length_le := coordinate_output_length_le w L

/-- Faithful rational bytes also lower-bound each signed numerator and denominator
bit length; therefore an encoded-vector upper bound really controls their sizes. -/
theorem rational_component_sizes_le_encoded (q : ℚ) :
    q.num.natAbs.size ≤ (rationalEncoding.encode q).length ∧
      q.den.size ≤ (rationalEncoding.encode q).length := by
  have hnum : q.num.natAbs ≤ Equiv.intEquivNat q.num := by
    cases q.num with
    | ofNat n => change n ≤ 2 * n; omega
    | negSucc n => change n + 1 ≤ 2 * n + 1; omega
  change _ ≤ (Computability.encodeNat (rationalCode q)).length ∧
    _ ≤ (Computability.encodeNat (rationalCode q)).length
  simp only [encodeNat_length]
  exact ⟨Nat.size_le_size (hnum.trans (Nat.left_le_pair _ _)),
    Nat.size_le_size (Nat.right_le_pair _ _)⟩

theorem coordinate_size_le_vector {n : ℕ} (v : Fin n → ℚ) (i : Fin n) :
    (rationalEncoding.encode (v i)).length ≤ ((vectorEncoding n).encode v).length := by
  change _ ≤ (vectorEncode n v).length
  rw [vectorEncode_length]
  have h := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
    Nat.zero_le (2 * (rationalEncoding.encode (v j)).length + 1)) (Finset.mem_univ i)
  omega

/-- Canonical reduced numerator and denominator sizes are individually polynomial
in original graph bits. Cancellation is fully accounted for by the arithmetic bound. -/
theorem output_coordinate_num_den_bits (w : Wiring) (L : Language) (G : Instance L)
    (i : Fin (Module.finrank ℚ L.coefficientField)) :
    (outputCoordinates w L G i).num.natAbs.size ≤
      (coordinateOutputPolynomial w L).eval ((inputEncoding L).encode G).length ∧
    (outputCoordinates w L G i).den.size ≤
      (coordinateOutputPolynomial w L).eval ((inputEncoding L).encode G).length := by
  have hv := (coordinate_size_le_vector (outputCoordinates w L G) i).trans
    (coordinate_output_length_le w L G)
  have h := rational_component_sizes_le_encoded (outputCoordinates w L G i)
  exact ⟨h.1.trans hv, h.2.trans hv⟩

end Paper2.ExactInput
