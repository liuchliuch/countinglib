import ComplexCSP.Complexity.WitnessRepair
import ComplexCSP.Complexity.EncodingBounds

/-! # Literal stored-witness bit bounds

All values are ordinary finite-domain tuple words. The table has n*d optional
slots, each holding at most n labels, plus one seed. Every header and option/list
frame is charged; no stored-code size oracle is supplied.
-/
namespace ComplexCSP.ComplexityWitnessSizeBounds
open MaltsevWitness ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityEncodingBounds PlanarHom PlanarHom.Complexity
variable {d n : ℕ}

noncomputable def tuplePolynomial (d : ℕ) : Polynomial ℕ := Polynomial.C (6*d+3)*Polynomial.X+1
noncomputable def maybePolynomial (d : ℕ) : Polynomial ℕ := Polynomial.C 6*tuplePolynomial d+4
noncomputable def tableRowPolynomial (d : ℕ) : Polynomial ℕ :=
  Polynomial.C (6*d)*maybePolynomial d+Polynomial.C (3*d+1)
noncomputable def tablePolynomial (d : ℕ) : Polynomial ℕ :=
  (Polynomial.C 6*tableRowPolynomial d+3)*Polynomial.X+1
noncomputable def storedPolynomial (d : ℕ) : Polynomial ℕ :=
  Polynomial.C 2*tablePolynomial d+maybePolynomial d+1

theorem word_code_bound (x : Tuple (Fin d) n) :
    (wordCode.encode (word x)).length ≤ (tuplePolynomial d).eval n := by
  have h := encoded_list_le BitEncoding.nat (word x) d (by
    intro a ha
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp ha
    exact (encodeNat_length_le c.val).trans c.isLt.le)
  simpa only [wordCode,word_length,tuplePolynomial,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_C,Polynomial.eval_X,Polynomial.eval_one] using h

theorem maybeWord_code_bound (x : Option (Tuple (Fin d) n)) :
    (maybeCode.encode (maybeWord x)).length ≤ (maybePolynomial d).eval n := by
  have hmem : ∀ w ∈ maybeWord x, (wordCode.encode w).length ≤ (tuplePolynomial d).eval n := by
    cases x with
    | none => simp [maybeWord]
    | some x =>
      intro w hw
      have he : w = word x := by simpa [maybeWord] using hw
      subst w
      exact word_code_bound x
  have hlen : (maybeWord x).length ≤ 1 := by cases x <;> simp [maybeWord]
  have h := encoded_list_le wordCode (maybeWord x) ((tuplePolynomial d).eval n) hmem
  change (wordCode.list.encode (maybeWord x)).length ≤ _
  simp only [maybePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_ofNat]
  nlinarith

theorem tableRow_code_bound (row : Vector (Option (Tuple (Fin d) n)) d) :
    (maybeCode.list.encode (row.toList.map maybeWord)).length ≤ (tableRowPolynomial d).eval n := by
  have h := encoded_list_le maybeCode (row.toList.map maybeWord) ((maybePolynomial d).eval n) (by
    intro a ha
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp ha
    exact maybeWord_code_bound v)
  simpa only [List.length_map,Vector.length_toList,tableRowPolynomial,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_C,Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc] using h

theorem rawTable_code_bound (W : StoredCode d n) :
    (tableCode.encode (rawTable W)).length ≤ (tablePolynomial d).eval n := by
  have h := encoded_list_le maybeCode.list (rawTable W) ((tableRowPolynomial d).eval n) (by
    intro a ha
    obtain ⟨row,_,rfl⟩ := List.mem_map.mp ha
    exact tableRow_code_bound row)
  simpa only [tableCode,rawTable,List.length_map,Vector.length_toList,tablePolynomial,
    Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_one,Polynomial.eval_ofNat] using h

/-- The literal encoding used by the actual class-membership machine. -/
theorem stored_code_bound (W : StoredCode d n) :
    ((tableCode.prod maybeCode).encode (rawTable W,maybeWord W.seed)).length ≤
      (storedPolynomial d).eval n := by
  have ht := rawTable_code_bound W
  have hs := maybeWord_code_bound W.seed
  rw [BitEncoding.prod_length]
  simp only [storedPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_one]
  omega

/-- The familiar semantic cell bound and the full bit bound hold together. -/
theorem stored_cells_and_bits (W : StoredCode d n) :
    W.cells ≤ n*(n*d+1) ∧
    ((tableCode.prod maybeCode).encode (rawTable W,maybeWord W.seed)).length ≤
      (storedPolynomial d).eval n := ⟨W.cells_le,stored_code_bound W⟩

end ComplexCSP.ComplexityWitnessSizeBounds
