import ComplexCSP.Instances.Basic
import ComplexCSP.Algebra.PowerSums

/-!
# The finite weight-profile foundation for exact counting reductions

The candidate assignment weights of a fixed finite language form a list of
polynomial cardinality in the number of constraints. Partition values are
exact weighted sums of the associated natural counts. These are semantic and
cardinality theorems, not a bit-machine polynomial-time reduction.
-/
namespace ComplexCSP.ComplexityWeightProfiles

open scoped BigOperators

/-- All exponent profiles with every exponent at most the number of factors.
The image removes collisions between equal products, including zero products. -/
def products {A K : Type} [Fintype A] [DecidableEq A]
    [CommMonoid K] [DecidableEq K] (w : A → K) (m : ℕ) : Finset K :=
  Finset.univ.image (fun e : A → Fin (m + 1) => ∏ i, w i ^ (e i).val)

theorem products_card_le {A K : Type} [Fintype A] [DecidableEq A]
    [CommMonoid K] [DecidableEq K] (w : A → K) (m : ℕ) :
    (products w m).card ≤ (m + 1) ^ Fintype.card A := by
  exact Finset.card_image_le.trans (by simp)

theorem list_prod_mem_products {A K : Type} [Fintype A] [DecidableEq A]
    [CommMonoid K] [DecidableEq K] (w : A → K) (l : List A)
    {m : ℕ} (hl : l.length ≤ m) : (l.map w).prod ∈ products w m := by
  let e : A → Fin (m + 1) := fun i =>
    ⟨l.count i, Nat.lt_succ_of_le (List.count_le_length.trans hl)⟩
  refine Finset.mem_image.mpr ⟨e, Finset.mem_univ _, ?_⟩
  dsimp [e]
  symm
  rw [Finset.prod_list_map_count]
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  simp only [List.mem_toFinset] at hi
  simp [List.count_eq_zero_of_not_mem hi]

variable {D K ι B H : Type} (L : Language D K ι)

/-- The fixed alphabet consists of table positions. Duplicate numeric values
are harmless, so this construction does not need field-element ordering. -/
abbrev Entry := (i : ι) × (Fin (L.arity i) → D)

def entryValue (i : Entry L) : K := L.value i.1 i.2

def entryLabels (I : Instance L B H) (a : B → D) (b : H → D) : List (Entry L) :=
  I.constraints.map (fun c => ⟨c.symbol, Sum.elim a b ∘ c.scope⟩)

@[simp] theorem entryLabels_length (I : Instance L B H) (a : B → D) (b : H → D) :
    (entryLabels L I a b).length = I.constraints.length := by simp [entryLabels]

theorem eval_eq_entry_product [CommMonoid K]
    (I : Instance L B H) (a : B → D) (b : H → D) :
    I.eval a b = ((entryLabels L I a b).map (entryValue L)).prod := by
  simp only [Instance.eval, entryLabels, List.map_map]
  rfl

variable [Fintype D] [Fintype ι] [DecidableEq D] [DecidableEq ι]

/-- A finite set depending only on the fixed language and constraint count. -/
def possibleWeights [CommMonoid K] [DecidableEq K] (m : ℕ) : Finset K :=
  products (entryValue L) m

theorem eval_mem_possibleWeights [CommMonoid K] [DecidableEq K]
    (I : Instance L B H) (a : B → D) (b : H → D) :
    I.eval a b ∈ possibleWeights L I.constraints.length := by
  rw [eval_eq_entry_product]
  exact list_prod_mem_products _ _ (by simp)

theorem possibleWeights_card_le [CommMonoid K] [DecidableEq K] (m : ℕ) :
    (possibleWeights L m).card ≤
      (m + 1) ^ (∑ i : ι, Fintype.card D ^ L.arity i) := by
  simpa [possibleWeights, Entry, Fintype.card_sigma, Fintype.card_fun] using
    products_card_le (entryValue L) m

variable [Fintype H] [DecidableEq H] [CommSemiring K] [DecidableEq K]

/-- The exact natural number of assignments with prescribed total weight. -/
def countAt (I : Instance L B H) (a : B → D) (z : K) : ℕ :=
  (Finset.univ.filter (fun b : H → D => I.eval a b = z)).card

omit [Fintype ι] [DecidableEq D] [DecidableEq ι] in
theorem countAt_le (I : Instance L B H) (a : B → D) (z : K) :
    countAt L I a z ≤ Fintype.card D ^ Fintype.card H := by
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The COUNT-to-partition formula, with collisions grouped exactly once. -/
theorem partition_eq_sum_counts (I : Instance L B H) (a : B → D) :
    I.partition a = ∑ z ∈ possibleWeights L I.constraints.length,
      (countAt L I a z : K) * z := by
  rw [Instance.partition]
  symm
  calc
    _ = ∑ z ∈ possibleWeights L I.constraints.length,
        ∑ b ∈ Finset.univ.filter (fun b : H → D => I.eval a b = z), I.eval a b := by
      apply Finset.sum_congr rfl
      intro z _
      rw [show (∑ b ∈ Finset.univ.filter (fun b : H → D => I.eval a b = z), I.eval a b) =
          ∑ _b ∈ Finset.univ.filter (fun b : H → D => I.eval a b = z), z from
        Finset.sum_congr rfl (fun b hb => (Finset.mem_filter.mp hb).2)]
      simp [countAt, nsmul_eq_mul]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun b _ => eval_mem_possibleWeights L I a b) (I.eval a)

/-- Repeat constraints while sharing all variables. Unlike powers of a marginal,
this operation raises each assignment weight before summing over assignments. -/
def repeatConstraints (I : Instance L B H) (q : ℕ) : Instance L B H :=
  ⟨(List.replicate q I.constraints).flatten⟩

omit [Fintype D] [Fintype ι] [DecidableEq D] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [CommSemiring K] [DecidableEq K] in
@[simp] theorem repeatConstraints_length (I : Instance L B H) (q : ℕ) :
    (repeatConstraints L I q).constraints.length = q * I.constraints.length := by
  induction q with
  | zero => simp [repeatConstraints]
  | succ q ih =>
    simp [repeatConstraints, List.replicate_succ, Nat.succ_mul, Nat.add_comm] at ih ⊢

omit [Fintype D] [Fintype ι] [DecidableEq D] [DecidableEq ι]
  [Fintype H] [DecidableEq H] [DecidableEq K] in
@[simp] theorem repeatConstraints_eval (I : Instance L B H) (q : ℕ)
    (a : B → D) (b : H → D) :
    (repeatConstraints L I q).eval a b = I.eval a b ^ q := by
  simp [repeatConstraints, Instance.eval, List.map_flatten, List.prod_flatten]

/-- The oracle query of repetition index `q` returns the `q`-th moment of the
assignment-weight histogram. The zeroth query retains all isolated variables. -/
theorem repeated_partition_eq_moment (I : Instance L B H) (a : B → D) (q : ℕ) :
    (repeatConstraints L I q).partition a =
      ∑ z ∈ possibleWeights L I.constraints.length, (countAt L I a z : K) * z ^ q := by
  simp only [Instance.partition, repeatConstraints_eval]
  symm
  calc
    _ = ∑ z ∈ possibleWeights L I.constraints.length,
        ∑ b ∈ Finset.univ.filter (fun b : H → D => I.eval a b = z), I.eval a b ^ q := by
      apply Finset.sum_congr rfl
      intro z _
      rw [show (∑ b ∈ Finset.univ.filter (fun b : H → D => I.eval a b = z), I.eval a b ^ q) =
          ∑ _b ∈ Finset.univ.filter (fun b : H → D => I.eval a b = z), z ^ q from
        Finset.sum_congr rfl (fun b hb => congrArg (· ^ q) (Finset.mem_filter.mp hb).2)]
      simp [countAt, nsmul_eq_mul]
    _ = _ := Finset.sum_fiberwise_of_maps_to
      (fun b _ => eval_mem_possibleWeights L I a b) (fun b => I.eval a b ^ q)

/-- Initial moments uniquely determine all coefficients, including the zero
weight. This is the exact interpolation algebra, without a runtime assertion. -/
theorem moments_injective {A F : Type} [Fintype A]
    [CommRing F] [IsDomain F] (w : A → F) (hw : Function.Injective w)
    (u v : A → F)
    (h : ∀ q < Fintype.card A, (∑ i, u i * w i ^ q) = ∑ i, v i * w i ^ q) :
    u = v := by
  classical
  by_contra hn
  have hd : ∃ i, u i - v i ≠ 0 := by
    by_contra! hz
    exact hn (funext (fun i => sub_eq_zero.mp (hz i)))
  obtain ⟨q, hq, hne⟩ := exists_weightedPowerSum_ne_zero_fintype
    (fun i => u i - v i) w hw hd
  apply hne
  simp only [weightedPowerSum, sub_mul, Finset.sum_sub_distrib, h q hq, sub_self]

end ComplexCSP.ComplexityWeightProfiles
