import Paper2.ReedMuller
import Paper2.BoundaryAction
import Paper2.EOCompletion
import Paper2.WeightedMatching
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The literal two-copy endpoint gadget and diagonal normalization in
Lemma 8.11, Q8.25--Q8.26, of arXiv:2610.00081v1. -/
namespace Paper2.ReedMullerNormalization
noncomputable section
open ReedMuller

abbrev Four := Fin 4 → Bool

def zeroWord {n : ℕ} : Fin n → Bool := fun _ => false
def oneWord {n : ℕ} : Fin n → Bool := fun _ => true
def compl {n : ℕ} (x : Fin n → Bool) : Fin n → Bool := fun j => !(x j)

/-- The printed information-set order: I0 = 000,100,010,001;
I1 = 011,101,110,111. -/
def join (u y : Four) : Word := ![u 0, u 3, u 2, y 0, u 1, y 1, y 2, y 3]

/-- Unique values on I0 extending the prescribed values on I1. -/
def extension (y : Four) : Four :=
  ![Bool.xor (y 0) (Bool.xor (y 1) (y 2)),
    Bool.xor (y 1) (Bool.xor (y 2) (y 3)),
    Bool.xor (y 0) (Bool.xor (y 2) (y 3)),
    Bool.xor (y 0) (Bool.xor (y 1) (y 3))]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem join_code (u y : Four) : IsCodeword (join u y) ↔ u = extension y := by
  revert u y
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem join_endpoints (u y : Four) :
    (join u y = zeroWord ↔ u = zeroWord ∧ y = zeroWord) ∧
    (join u y = oneWord ↔ u = oneWord ∧ y = oneWord) := by
  revert u y
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem central_iff_code_nonconstant (x : Word) :
    IsCentral x ↔ IsCodeword x ∧ x ≠ zeroWord ∧ x ≠ oneWord := by
  revert x
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem extension_complement (y z : Four) :
    compl (extension y) = extension z ↔ z = compl y := by
  revert y z
  decide +kernel

@[simp] theorem extension_zero : extension zeroWord = zeroWord := by decide +kernel
@[simp] theorem extension_one : extension oneWord = oneWord := by decide +kernel
@[simp] theorem compl_zero {n : ℕ} : compl (zeroWord (n := n)) = oneWord := rfl
@[simp] theorem compl_one {n : ℕ} : compl (oneWord (n := n)) = zeroWord := rfl
@[simp] theorem compl_compl {n : ℕ} (x : Fin n → Bool) : compl (compl x) = x := by
  funext i
  simp [compl]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem central_join (u y : Four) :
    IsCentral (join u y) ↔ u = extension y ∧ y ≠ zeroWord ∧ y ≠ oneWord := by
  revert u y
  decide +kernel

@[simp] theorem zero_ne_one_four : (zeroWord : Four) ≠ oneWord := by decide +kernel
@[simp] theorem one_ne_zero_four : (oneWord : Four) ≠ zeroWord := by decide +kernel

variable {K : Type*} [CommRing K]

/-- Endpoint deltas and the central layer, with their actual coefficients. -/
def source (A B c : K) : Signature K 8 := fun x =>
  (if x = zeroWord then A else 0) + (if x = oneWord then B else 0) +
    c * central x

def choice (A B c : K) (y : Four) : K :=
  if y = zeroWord then A else if y = oneWord then B else c

/-- The information-set coefficient formula, including all zero entries. -/
theorem source_join (A B c : K) (u y : Four) :
    source A B c (join u y) = if u = extension y then choice A B c y else 0 := by
  simp only [source, central, central_join, (join_endpoints u y).1,
    (join_endpoints u y).2, choice]
  by_cases hy0 : y = zeroWord
  · subst y
    simp
  · by_cases hy1 : y = oneWord
    · subst y
      simp [hy0]
    · simp [hy0, hy1]

/-- Four independent native X edges, retaining both internal bit sums. -/
def joined (A B c : K) (y z : Four) : K :=
  ∑ u : Four, ∑ v : Four,
    (∏ j : Fin 4, Bell.X (u j) (v j)) * source A B c (join u y) *
      source A B c (join v z)

theorem prod_native_X (u v : Four) :
    (∏ j : Fin 4, Bell.X (K := K) (u j) (v j)) =
      if v = compl u then 1 else 0 := by
  have h : ∀ a b : Bool, Bell.X (K := K) a b = if b = !a then 1 else 0 := by
    intro a b
    cases a <;> cases b <;> rfl
  simp only [h, Fintype.prod_boole, compl, funext_iff]
  split_ifs <;> rfl

/-- First eliminate precisely the four X-edge constraints. -/
theorem joined_eliminate_edges (A B c : K) (y z : Four) :
    joined A B c y z = ∑ u : Four,
      source A B c (join u y) * source A B c (join (compl u) z) := by
  simp only [joined, prod_native_X]
  simp

/-- The explicit affine extensions eliminate the remaining internal sum. -/
theorem joined_unique_extension (A B c : K) (y z : Four) :
    joined A B c y z =
      if z = compl y then choice A B c y * choice A B c z else 0 := by
  rw [joined_eliminate_edges]
  simp only [source_join]
  rw [Finset.sum_eq_single (extension y)]
  · simp [extension_complement]
  · intro u _ hu
    simp [hu]
  · simp

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem compl_endpoints (y : Four) :
    (compl y = zeroWord ↔ y = oneWord) ∧
    (compl y = oneWord ↔ y = zeroWord) := by
  revert y
  decide +kernel

def fourCoefficient (A B c : K) (y : Four) : K :=
  if y = zeroWord ∨ y = oneWord then A * B else c ^ 2

theorem choice_complement_product (A B c : K) (y : Four) :
    choice A B c y * choice A B c (compl y) = fourCoefficient A B c y := by
  simp only [choice, (compl_endpoints y).1, (compl_endpoints y).2, fourCoefficient]
  by_cases h0 : y = zeroWord
  · subst y
    simp [zeroWord, oneWord, funext_iff]
  · by_cases h1 : y = oneWord
    · simp [h1, mul_comm]
    · simp [h0, h1, pow_two]

/-- Q8.25's four-pair coefficient function, derived from the actual native sum. -/
theorem joined_formula (A B c : K) (y z : Four) :
    joined A B c y z = if z = compl y then fourCoefficient A B c y else 0 := by
  rw [joined_unique_extension]
  split_ifs with h
  · subst z
    exact choice_complement_product A B c y
  · rfl

/-- Interleave the four surviving opposite pairs before the last closure. -/
def eightOutput (A B c : K) : Signature K 8 := fun x =>
  joined A B c ![x 0, x 2, x 4, x 6] ![x 1, x 3, x 5, x 7]

/-- The actual fifth native-X closure, leaving six explicitly ordered ports. -/
def sixOutput (A B c : K) : Signature K 6 :=
  Signature.contract Bell.X (eightOutput A B c)

def Opposite (x : Fin 6 → Bool) : Prop :=
  x 1 = !(x 0) ∧ x 3 = !(x 2) ∧ x 5 = !(x 4)
instance (x : Fin 6 → Bool) : Decidable (Opposite x) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def Antipodal (x : Fin 6 → Bool) : Prop :=
  (x 0 = false ∧ x 2 = false ∧ x 4 = false) ∨
  (x 0 = true ∧ x 2 = true ∧ x 4 = true)
instance (x : Fin 6 → Bool) : Decidable (Antipodal x) :=
  inferInstanceAs (Decidable ((_ ∧ _ ∧ _) ∨ (_ ∧ _ ∧ _)))

set_option maxHeartbeats 0 in
/-- All 64 six-port coefficients of the literal five-edge construction. -/
theorem sixOutput_formula (A B c : K) (x : Fin 6 → Bool) :
    sixOutput A B c x = if Opposite x then
      (if Antipodal x then A * B + c ^ 2 else 2 * c ^ 2) else 0 := by
  rw [sixOutput, Bell.X_eq_disequality, Signature.contract_disequality]
  simp only [eightOutput, joined_formula]
  have he : x = ![x 0, x 1, x 2, x 3, x 4, x 5] := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;>
    norm_num [fourCoefficient, compl, zeroWord, oneWord, Opposite, Antipodal,
      funext_iff, Fin.forall_fin_succ] <;> ring

/-- Compress the three adjacent opposite pairs, retaining their orientations. -/
def pairWord (y : Fin 3 → Bool) : Fin 6 → Bool :=
  ![y 0, !(y 0), y 1, !(y 1), y 2, !(y 2)]

/-- The displayed minor is taken in the real coefficient tensor of the gadget. -/
theorem sixOutput_minor (A B c : K) :
    sixOutput A B c (pairWord ![false, false, false]) *
        sixOutput A B c (pairWord ![false, true, true]) -
      sixOutput A B c (pairWord ![false, false, true]) *
        sixOutput A B c (pairWord ![false, true, false]) =
      2 * c ^ 2 * (A * B - c ^ 2) := by
  simp only [sixOutput_formula]
  norm_num [pairWord, Opposite, Antipodal]
  ring

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem opposite_central (x : Fin 6 → Bool) (hx : Opposite x) :
    2 * Paper2.weight x = 6 := by
  revert x
  decide +kernel

/-- The six-port output is an EO tensor, even in the antipodal cancellation case. -/
theorem sixOutput_centralSupport (A B c : K) : Signature.CentralSupport (sixOutput A B c) := by
  intro x hx
  have ho : ¬Opposite x := fun h => hx (opposite_central x h)
  simp [sixOutput_formula, ho]

section Nonzero
variable [IsDomain K] [CharZero K]

theorem twice_square_ne_zero (c : K) (hc : c ≠ 0) : 2 * c ^ 2 ≠ 0 :=
  mul_ne_zero (by norm_num) (pow_ne_zero _ hc)

/-- The construction is never the zero tensor when the central coefficient is nonzero. -/
theorem sixOutput_ne_zero (A B c : K) (hc : c ≠ 0) : sixOutput A B c ≠ 0 := by
  intro h
  have he := congrFun h (pairWord ![false, false, true])
  have hz : 2 * c ^ 2 = 0 := by
    simpa [sixOutput_formula, pairWord, Opposite, Antipodal] using he
  exact twice_square_ne_zero c hc hz

theorem sixOutput_minor_ne_zero (A B c : K) (hc : c ≠ 0) (hab : A * B ≠ c ^ 2) :
    sixOutput A B c (pairWord ![false, false, false]) *
        sixOutput A B c (pairWord ![false, true, true]) -
      sixOutput A B c (pairWord ![false, false, true]) *
        sixOutput A B c (pairWord ![false, true, false]) ≠ 0 := by
  rw [sixOutput_minor]
  exact mul_ne_zero (twice_square_ne_zero c hc) (sub_ne_zero.mpr hab)

/-- When AB=-c² precisely the two antipodal choices disappear. -/
theorem sixOutput_exceptional_support (A B c : K) (hc : c ≠ 0)
    (hab : A * B = -c ^ 2) (x : Fin 6 → Bool) :
    sixOutput A B c x ≠ 0 ↔ Opposite x ∧ ¬Antipodal x := by
  rw [sixOutput_formula, hab]
  by_cases ho : Opposite x <;> by_cases ha : Antipodal x <;>
    simp [ho, ha, twice_square_ne_zero c hc]

/-- Otherwise all eight independent pair choices survive. -/
theorem sixOutput_full_support (A B c : K) (hc : c ≠ 0)
    (hab : A * B ≠ -c ^ 2) (x : Fin 6 → Bool) :
    sixOutput A B c x ≠ 0 ↔ Opposite x := by
  have hd : A * B + c ^ 2 ≠ 0 := by
    intro h
    apply hab
    exact eq_neg_of_add_eq_zero_left h
  rw [sixOutput_formula]
  by_cases ho : Opposite x <;> by_cases ha : Antipodal x <;>
    simp [ho, ha, hd, twice_square_ne_zero c hc]

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sixOutput_exceptional_card (A B c : K) (hc : c ≠ 0)
    (hab : A * B = -c ^ 2) :
    ((Finset.univ : Finset (Fin 6 → Bool)).filter (fun x => sixOutput A B c x ≠ 0)).card = 6 := by
  classical
  simp only [sixOutput_exceptional_support A B c hc hab]
  decide +kernel

open Classical in
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sixOutput_full_card (A B c : K) (hc : c ≠ 0)
    (hab : A * B ≠ -c ^ 2) :
    ((Finset.univ : Finset (Fin 6 → Bool)).filter (fun x => sixOutput A B c x ≠ 0)).card = 8 := by
  classical
  simp only [sixOutput_full_support A B c hc hab]
  decide +kernel

omit [IsDomain K] [CharZero K] in
/-- Identification with the exact weighted-matching obstruction proved separately. -/
theorem sixOutput_eq_twoLevel (A B c : K) :
    sixOutput A B c = WeightedMatching.twoLevel (A * B + c ^ 2) (2 * c ^ 2) := by
  funext x
  exact sixOutput_formula A B c x

/-- Outside the endpoint invariant, the output is outside source-exact B×,
including every orientation and every weighted opposite-pair matching. -/
theorem sixOutput_not_weightedMatching (A B c : K) (hc : c ≠ 0)
    (hab : A * B ≠ c ^ 2) : ¬WeightedMatching.IsProduct (sixOutput A B c) := by
  rw [sixOutput_eq_twoLevel]
  apply WeightedMatching.twoLevel_not_isProduct (twice_square_ne_zero c hc)
  intro he
  apply hab
  linear_combination he

end Nonzero

section Diagonal
variable {F : Type*} [Field F]

/-- D(s)=diag(s,s⁻¹), with ordinary bilinear coordinates. -/
def diagonal (s : F) : Kernel F := fun a b =>
  (if a then s⁻¹ else s) * Signature.equality a b

/-- A diagonal action collapses the full tensor sum to its single diagonal term. -/
theorem diagonal_action {n : ℕ} (s : F) (f : Signature F n) (x : Fin n → Bool) :
    Signature.coordinateAction (fun _ => diagonal s) f x =
      (∏ i : Fin n, if x i then s⁻¹ else s) * f x := by
  simp only [Signature.coordinateAction, diagonal, Finset.prod_mul_distrib,
    Signature.prod_equality]
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · simp

theorem diagonal_factor (s : F) (x : Word) :
    (∏ i : Fin 8, if x i then s⁻¹ else s) =
      s ^ ReedMuller.weight (compl x) * (s⁻¹) ^ ReedMuller.weight x := by
  have h : ∀ b : Bool, (if b then s⁻¹ else s) =
      s ^ (!b).toNat * (s⁻¹) ^ b.toNat := by
    intro b
    cases b <;> simp
  simp only [h, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ReedMuller.weight, compl]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem central_complement_weight (x : Word) (hx : IsCentral x) :
    ReedMuller.weight (compl x) = 4 := by
  revert x
  decide +kernel

/-- The weight-four diagonal factor is exactly one, including its scalar. -/
theorem diagonal_central_factor (s : F) (hs : s ≠ 0) (x : Word)
    (hx : IsCentral x) : (∏ i : Fin 8, if x i then s⁻¹ else s) = 1 := by
  rw [diagonal_factor, central_complement_weight x hx, hx.2, inv_pow]
  exact mul_inv_cancel₀ (pow_ne_zero _ hs)

/-- The ordinary-transpose congruence preserves the native X edge exactly. -/
theorem diagonal_preserves_X (s : F) (hs : s ≠ 0) :
    Kernel.mul (Kernel.mul (Kernel.transpose (diagonal s)) Bell.X)
      (diagonal s) = Bell.X := by
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.mul_apply, Kernel.transpose, diagonal, Signature.equality,
      Bell.X, Bell.ordered, Bell.sign, hs]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem codeword_cases (x : Word) (hx : IsCodeword x) :
    x = zeroWord ∨ x = oneWord ∨ IsCentral x := by
  revert x
  decide +kernel

@[simp] theorem zero_codeword : IsCodeword (zeroWord : Word) := by decide +kernel
@[simp] theorem one_codeword : IsCodeword (oneWord : Word) := by decide +kernel
@[simp] theorem zero_not_central : ¬IsCentral (zeroWord : Word) := by decide +kernel
@[simp] theorem one_not_central : ¬IsCentral (oneWord : Word) := by decide +kernel
@[simp] theorem zero_ne_one_eight : (zeroWord : Word) ≠ oneWord := by decide +kernel
@[simp] theorem one_ne_zero_eight : (oneWord : Word) ≠ zeroWord := by decide +kernel

/-- Q8.26, as the genuine eight-slot coordinateAction, not a weight-scaling proxy. -/
theorem diagonal_normalization (A B c s : F) (hA : A ≠ 0) (hc : c ≠ 0)
    (hAB : A * B = c ^ 2) (hs8 : s ^ 8 = c / A) :
    Signature.coordinateAction (fun _ => diagonal s) (source A B c) =
      fun x => c * core x := by
  have hs : s ≠ 0 := by
    intro hz
    apply div_ne_zero hc hA
    rw [← hs8, hz]
    simp
  have hAs : s ^ 8 * A = c := by rw [hs8]; field_simp
  have hBs : (s⁻¹) ^ 8 * B = c := by
    rw [inv_pow, hs8]
    field_simp
    linear_combination hAB
  funext x
  rw [diagonal_action]
  by_cases hx : IsCodeword x
  · rcases codeword_cases x hx with h0 | h1 | hcen
    · subst x
      simpa [zeroWord, source, central, core] using hAs
    · subst x
      simpa [oneWord, source, central, core] using hBs
    · have hh := (central_iff_code_nonconstant x).mp hcen
      rw [diagonal_central_factor s hs x hcen]
      simp [source, central, core, hcen, hx, hh.2.1, hh.2.2]
  · have h0 : x ≠ zeroWord := by rintro rfl; exact hx zero_codeword
    have h1 : x ≠ oneWord := by rintro rfl; exact hx one_codeword
    have hcen : ¬IsCentral x := fun h => hx h.1
    simp [source, central, core, hx, h0, h1, hcen]

/-- Eighth roots exist in any algebraically closed coefficient field. -/
theorem exists_normalizing_root [IsAlgClosed F] (A c : F) (hA : A ≠ 0) (hc : c ≠ 0) :
    ∃ s : F, s ≠ 0 ∧ s ^ 8 = c / A := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (c / A) (by decide : 0 < 8)
  refine ⟨s, ?_, hs⟩
  intro hz
  apply div_ne_zero hc hA
  rw [← hs, hz]
  simp

/-- The literal endpoint repair dichotomy in Lemma 8.11. The first alternative
is the fixed two-source, five-native-X-edge construction defined above. -/
theorem canonical_endpoint_repair [CharZero F] (A B c : F)
    (hnz : A * B * c ≠ 0) :
    (sixOutput A B c ≠ 0 ∧ Signature.CentralSupport (sixOutput A B c) ∧
      ¬WeightedMatching.IsProduct (sixOutput A B c)) ∨
    (A * B = c ^ 2 ∧ ∀ s : F, s ^ 8 = c / A →
      Signature.coordinateAction (fun _ => diagonal s) (source A B c) =
        (fun x => c * core x) ∧
      Kernel.mul (Kernel.mul (Kernel.transpose (diagonal s)) Bell.X)
        (diagonal s) = Bell.X) := by
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hnz).2
  have hA : A ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hnz).1).1
  by_cases hab : A * B = c ^ 2
  · right
    refine ⟨hab, fun s hs => ⟨diagonal_normalization A B c s hA hc hab hs, ?_⟩⟩
    apply diagonal_preserves_X
    intro hz
    apply div_ne_zero hc hA
    rw [← hs, hz]
    simp
  · exact Or.inl ⟨sixOutput_ne_zero A B c hc, sixOutput_centralSupport A B c,
      sixOutput_not_weightedMatching A B c hc hab⟩

end Diagonal
end
end Paper2.ReedMullerNormalization
