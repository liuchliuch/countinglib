import PlanarHom.FiniteLabelLookupMachines

/-! # Genuine FP lookup into fixed tables with arbitrary encoded output values -/
namespace ComplexCSP.ComplexityFiniteLookup
open PlanarHom PlanarHom.Complexity

variable {A : Type}

def lookup (default : A) : List (ℕ × A) → ℕ → A
  | [],_ => default
  | (i,value)::rest,n => if n=i then value else lookup default rest n

/-- Each value is a fixed finite machine constant; the query is a binary index. -/
theorem fp_lookup (encoding : BitEncoding A) (default : A) (table : List (ℕ × A)) :
    FP BitEncoding.nat encoding (lookup default table) := by
  induction table with
  | nil => exact fp_const _ _ default
  | cons entry rest ih =>
    have hp := ((fp_id BitEncoding.nat).pair (fp_const BitEncoding.nat BitEncoding.nat entry.1)).comp
      PlanarHom.NatListSumMachines.fp_equal
    exact hp.ite (fp_const BitEncoding.nat encoding entry.2) ih

 theorem lookup_eq_of_mem (default : A) (table : List (ℕ × A)) (key : ℕ) (value : A)
    (hmem : (key,value) ∈ table)
    (hunique : ∀ p ∈ table, p.1 = key → p.2 = value) :
    lookup default table key = value := by
  induction table with
  | nil => simp at hmem
  | cons p rest ih =>
    by_cases hp : key=p.1
    · rw [lookup,if_pos hp]
      exact hunique p (List.mem_cons_self) hp.symm
    · rw [lookup,if_neg hp]
      apply ih
      · rcases List.mem_cons.mp hmem with h | h
        · exact False.elim (hp (congrArg Prod.fst h))
        · exact h
      · intro q hq
        exact hunique q (List.mem_cons_of_mem p hq)

 theorem lookup_fin_table {s : ℕ} (default : A) (value : Fin s → A) (i : Fin s) :
    lookup default (List.ofFn (fun j : Fin s => (j.val,value j))) i.val = value i := by
  apply lookup_eq_of_mem
  · exact List.mem_ofFn.mpr ⟨i,rfl⟩
  · intro p hp he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hp
    exact congrArg value (Fin.ext he)

end ComplexCSP.ComplexityFiniteLookup
