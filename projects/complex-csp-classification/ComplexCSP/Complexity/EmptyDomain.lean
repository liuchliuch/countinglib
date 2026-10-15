import ComplexCSP.Complexity.CSPValidation

/-! # Genuine FP evaluation on the empty-domain boundary

Positive signature arities rule out a valid constraint on zero variables. For
all raw codes the existing malformed-unit convention therefore gives value one
at zero variables and zero at any positive variable count.
-/
namespace ComplexCSP.ComplexityEmptyDomain
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityCSPCode
variable {D K : Type} {s : ℕ} (L : Language D K (Fin s))

theorem constraint_invalid_on_zero (c : ℕ × List ℕ) : ¬ConstraintValid L 0 c := by
  rintro ⟨hs,hlen,hvars⟩
  cases he : c.2 with
  | nil =>
    have hp := L.arity_pos ⟨c.1,hs⟩
    simp only [he, List.length_nil] at hlen
    omega
  | cons v rest =>
    have hv : v ∈ c.2 := by rw [he]; exact List.mem_cons_self
    exact Nat.not_lt_zero _ (hvars v hv)

variable [Fintype D] [IsEmpty D]

section Semantics
variable [CommSemiring K]

omit [IsEmpty D] in
theorem partition_zero_vertices (cs : List (ℕ × List ℕ)) :
    partition L ⟨0,cs⟩ = 1 := by
  classical
  simp only [partition, Fintype.sum_unique, eval, assignmentWord, List.map_map]
  apply List.prod_eq_one
  intro a ha
  obtain ⟨c,_,rfl⟩ := List.mem_map.mp ha
  dsimp only [Function.comp_apply]
  simp [constraintEntry, constraint_invalid_on_zero, entryValue]

theorem partition_eq (g : Code) : partition L g = if g.vertices = 0 then 1 else 0 := by
  classical
  by_cases hg : g.vertices = 0
  · rcases g with ⟨n,cs⟩
    change n = 0 at hg
    subst n
    simpa using partition_zero_vertices L cs
  · letI : IsEmpty (Fin g.vertices → D) :=
      ⟨fun σ => isEmptyElim (σ ⟨0,Nat.pos_of_ne_zero hg⟩)⟩
    simp [partition,hg]

end Semantics

section Machines
variable [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

theorem fp_partition : FP encoding (numberFieldEncoding basis) (partition L) := by
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hn := (hv.comp (fp_fst BitEncoding.unaryNat constraintEncoding.list)).comp
    UnaryNatConversionMachine.fp_conversion
  have hz := (hn.pair (fp_const encoding BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  exact (hz.ite (fp_const encoding (numberFieldEncoding basis) 1)
    (fp_const encoding (numberFieldEncoding basis) 0)).congr (fun g => (partition_eq L g).symm)

end Machines
end ComplexCSP.ComplexityEmptyDomain
