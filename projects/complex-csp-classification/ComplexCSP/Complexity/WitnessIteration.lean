import ComplexCSP.Complexity.WitnessRepair

/-! # Polynomially bounded iteration of the literal witness repair

The iteration list carries the coordinate indices; no binary counter is expanded
without an explicit unary budget. The materialized table and target are copied
unchanged. Every returned word has at most the initial word length and fixed
finite-alphabet entries, which gives a linear intermediate-codeword bound.
-/
namespace ComplexCSP.ComplexityWitnessPrimitives
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ListFlattenMachines

variable (d : ℕ) (m : Fin d → Fin d → Fin d → Fin d)

theorem operation_le (x y z : ℕ) : operation d m x y z ≤ d := by
  unfold operation
  split <;> rename_i hx
  · split <;> rename_i hy
    · split <;> rename_i hz
      · exact Nat.le_of_lt (m ⟨x,hx⟩ ⟨y,hy⟩ ⟨z,hz⟩).isLt
      · omega
    · omega
  · omega

theorem mapOperation_entry_le (xs ys zs : List ℕ) :
    ∀ v ∈ mapOperation d m xs ys zs, v ≤ d := by
  intro v hv
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hv
  exact operation_le d m _ _ _

theorem mapOperation_code_bound (xs ys zs : List ℕ) :
    (wordCode.encode (mapOperation d m xs ys zs)).length ≤
      (6*d+9)*xs.length+1 := by
  let out := mapOperation d m xs ys zs
  have hv : ∀ v ∈ out, (BitEncoding.nat.encode v).length ≤ d+1 := by
    intro v hv
    have h := encodeNat_length_le v
    have h' := mapOperation_entry_le d m xs ys zs v hv
    omega
  have hs := ListMapMachines.sum_map_le_mul (fun v => (BitEncoding.nat.encode v).length)
    out (d+1) hv
  have hw := word_length_le_payload BitEncoding.nat out
  rw [payloadSize_eq] at hw
  have hl : out.length = xs.length := mapOperation_length d m xs ys zs
  dsimp only [wordCode]
  dsimp only [out] at hs hw hl
  nlinarith

theorem repairWord_head_length (p : RepairInput) :
    ((repairWord d m p).headD []).length ≤ p.2.2.2.length := by
  unfold repairWord
  dsimp only
  split
  · simp
  · split
    · simp
    · split <;> simp [mapOperation_length]

theorem repairWord_code_bound (p : RepairInput) :
    (maybeCode.encode (repairWord d m p)).length ≤
      100*(d+1)*(p.2.2.2.length+1) := by
  have hnil : (maybeCode.encode []).length ≤ 1 := by
    simpa [payloadSize_eq] using word_length_le_payload wordCode []
  have hsome (u v : List ℕ) :
      (maybeCode.encode [mapOperation d m p.2.2.2 u v]).length ≤
        100*(d+1)*(p.2.2.2.length+1) := by
    have hw := word_length_le_payload wordCode [mapOperation d m p.2.2.2 u v]
    rw [payloadSize_eq] at hw
    simp only [List.map_singleton, List.sum_singleton, List.length_singleton] at hw
    have hm := mapOperation_code_bound d m p.2.2.2 u v
    change (maybeCode.encode _).length ≤ _ at hw
    nlinarith
  unfold repairWord
  dsimp only
  split <;> rename_i h
  · nlinarith
  split <;> rename_i h'
  · nlinarith
  split
  · exact hsome _ _
  · nlinarith

/-- Missing current witnesses remain missing; malformed multiple-element lists
are safely reduced to their first word by the total raw implementation. -/
def advance (table : RawTable) (target : List ℕ) (cur : MaybeWord) (i : ℕ) : MaybeWord :=
  if cur = [] then [] else repairWord d m (table,i,target,cur.headD [])

theorem advance_head_length (table : RawTable) (target : List ℕ) (cur : MaybeWord) (i : ℕ) :
    ((advance d m table target cur i).headD []).length ≤ (cur.headD []).length := by
  unfold advance
  split
  · simp
  · exact repairWord_head_length d m _

theorem advance_code_bound (table : RawTable) (target : List ℕ) (cur : MaybeWord) (i : ℕ) :
    (maybeCode.encode (advance d m table target cur i)).length ≤
      100*(d+1)*((cur.headD []).length+1) := by
  unfold advance
  split
  · have h := word_length_le_payload wordCode []
    simp only [payloadSize_eq, List.map_nil, List.sum_nil, List.length_nil] at h
    change (maybeCode.encode []).length ≤ _ at h
    nlinarith
  · exact repairWord_code_bound d m _

theorem fold_advance_head_length (table : RawTable) (target : List ℕ)
    (cur : MaybeWord) (indices : List ℕ) :
    ((indices.foldl (advance d m table target) cur).headD []).length ≤
      (cur.headD []).length := by
  induction indices generalizing cur with
  | nil => exact le_rfl
  | cons i rest ih =>
    exact (ih _).trans (advance_head_length d m table target cur i)

theorem fold_advance_code_max (table : RawTable) (target : List ℕ)
    (cur : MaybeWord) (indices : List ℕ) :
    (maybeCode.encode (indices.foldl (advance d m table target) cur)).length ≤
      max (maybeCode.encode cur).length (100*(d+1)*((cur.headD []).length+1)) := by
  induction indices generalizing cur with
  | nil => exact le_max_left _ _
  | cons i rest ih =>
    have hc := advance_code_bound d m table target cur i
    have hh := advance_head_length d m table target cur i
    calc
      _ ≤ max (maybeCode.encode (advance d m table target cur i)).length
          (100*(d+1)*(((advance d m table target cur i).headD []).length+1)) := ih _
      _ ≤ 100*(d+1)*((cur.headD []).length+1) :=
        max_le hc (Nat.mul_le_mul_left _ (Nat.add_le_add_right hh 1))
      _ ≤ _ := le_max_right _ _

theorem fold_advance_code_bound (table : RawTable) (target : List ℕ)
    (cur : MaybeWord) (indices : List ℕ) :
    (maybeCode.encode (indices.foldl (advance d m table target) cur)).length ≤
      (maybeCode.encode cur).length + 100*(d+1)*((cur.headD []).length+1) :=
  (fold_advance_code_max d m table target cur indices).trans (max_le (by omega) (by omega))

theorem head_word_length_le_code (cur : MaybeWord) :
    (cur.headD []).length ≤ (maybeCode.encode cur).length := by
  cases cur with
  | nil => simp
  | cons w rest =>
    have hl := BitEncoding.list_length_le BitEncoding.nat w
    have hm := ListMapMachines.mem_le_sum_map (fun x => (wordCode.encode x).length)
      (show w ∈ w::rest from List.mem_cons_self)
    have hp := payloadSize_le_word wordCode (w::rest)
    rw [payloadSize_eq] at hp
    simp only [List.headD_cons]
    change _ ≤ (wordCode.list.encode (w::rest)).length
    change w.length ≤ (wordCode.encode w).length at hl
    omega

abbrev WitnessState := RawTable × (List ℕ × MaybeWord)
abbrev witnessStateCode : BitEncoding WitnessState := tableCode.prod (wordCode.prod maybeCode)

def witnessStep (state : WitnessState) (i : ℕ) : WitnessState :=
  (state.1, state.2.1, advance d m state.1 state.2.1 state.2.2 i)

@[simp] theorem fold_witnessStep (table : RawTable) (target : List ℕ)
    (cur : MaybeWord) (indices : List ℕ) :
    indices.foldl (witnessStep d m) (table,target,cur) =
      (table,target,indices.foldl (advance d m table target) cur) := by
  induction indices generalizing cur with
  | nil => rfl
  | cons i rest ih => simpa only [List.foldl_cons, witnessStep] using ih (advance d m table target cur i)

/-- An explicit linear bound for every intermediate fold state. It holds even
on malformed raw tables and for arbitrary coordinate lists. -/
theorem witnessStep_prefix_bound (state : WitnessState) (indices : List ℕ) (i : ℕ) :
    (witnessStateCode.encode ((indices.take i).foldl (witnessStep d m) state)).length ≤
      (Polynomial.C (100*(d+1)+2) * (Polynomial.X+1)).eval
        ((witnessStateCode.prod BitEncoding.nat.list).encode (state,indices)).length := by
  rcases state with ⟨table,target,cur⟩
  rw [fold_witnessStep]
  have hb := fold_advance_code_bound d m table target cur (indices.take i)
  have hh := head_word_length_le_code cur
  let N := ((witnessStateCode.prod BitEncoding.nat.list).encode ((table,target,cur),indices)).length
  have hs : (witnessStateCode.encode (table,target,cur)).length ≤ N := by
    dsimp only [N]
    simp only [BitEncoding.prod_length]
    omega
  have hc : (maybeCode.encode cur).length ≤ (witnessStateCode.encode (table,target,cur)).length := by
    simp only [witnessStateCode, BitEncoding.prod_length]
    omega
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one]
  change _ ≤ (100*(d+1)+2)*(N+1)
  simp only [witnessStateCode, BitEncoding.prod_length] at hs hc ⊢
  nlinarith

end ComplexCSP.ComplexityWitnessPrimitives
