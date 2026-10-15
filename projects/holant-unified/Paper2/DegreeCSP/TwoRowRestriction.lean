import Paper2.DegreeCSP.OrderedPresentation
import Paper2.PrimeFactorization.PointMass

/-! A literal degree-preserving compiler selecting any two rows and retaining
one column. Its helper variables are forced, so its value has no extra scalar.
Every added clause is repeated exactly k times. -/
namespace Paper2.DegreeCSP.TwoRowRestriction
open scoped BigOperators
open Tractable TensorDecomposition
noncomputable section
attribute [local instance] Classical.propDecidable
local instance (priority := 2000) (α : Type) : DecidableEq α := Classical.decEq α

def twoRow {n : ℕ} (f : Signature AlgebraicComplex (n + 1))
    (a b : Fin n → Bool) : Signature AlgebraicComplex 2 :=
  fun z => f (Fin.snoc (if z 0 then b else a) (z 1))

abbrev rowBit (a b s : Bool) : Bool := if s then b else a
abbrev auxBit (a b s : Bool) : Bool := if a = false ∧ b = true then !s else false

abbrev clauseArity : Bool → Bool → Bool → ℕ
  | false, true, _ => 2
  | true, false, false => 2
  | _, _, _ => 1

abbrev clauseTable (a b c : Bool) : Signature AlgebraicComplex (clauseArity a b c) :=
  match a, b, c with
  | false, true, _ => kernelSignature Signature.disequality
  | true, false, false => kernelSignature Signature.disequality
  | false, false, false => literalPin false
  | true, true, false => literalPin true
  | false, false, true => literalPin false
  | true, false, true => literalPin false
  | true, true, true => literalPin false

abbrev clauseScope {V : Type} (s h u : V) (a b c : Bool) :
    Fin (clauseArity a b c) → V :=
  match a, b, c with
  | false, true, false => ![s,u]
  | false, true, true => ![h,u]
  | true, false, false => ![s,h]
  | false, false, false => fun _ => h
  | true, true, false => fun _ => h
  | _, _, true => fun _ => u

theorem clause_product (a b s h u : Bool) :
    (∏ c : Bool, clauseTable a b c (clauseScope s h u a b c)) =
      if h = rowBit a b s ∧ u = auxBit a b s then 1 else 0 := by
  cases a <;> cases b <;> cases s <;> cases h <;> cases u <;>
    simp [clauseTable,clauseScope,literalPin,
      kernelSignature,Signature.disequality,rowBit,auxBit]

abbrev Extra (n : ℕ) := Fin n ⊕ Fin n
abbrev Hidden {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1))) :=
  Fin P.hiddenCount ⊕ Extra n
abbrev Tag {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1))) (k : ℕ) :=
  Fin P.constraints ⊕ (Fin n × (Fin k × Bool))

abbrev embed {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1))) :
    Fin (n + 1) ⊕ Fin P.hiddenCount → Fin 2 ⊕ Hidden P
  | Sum.inl i => Fin.lastCases (Sum.inl 1) (fun j => Sum.inr (Sum.inr (Sum.inl j))) i
  | Sum.inr j => Sum.inr (Sum.inl j)

theorem embed_injective {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1))) :
    Function.Injective (embed P) := by
  intro v w h
  cases v with
  | inl v =>
    cases w with
    | inl w =>
      induction v using Fin.lastCases with
      | last =>
        induction w using Fin.lastCases with
        | last => rfl
        | cast w => simp [embed] at h
      | cast v =>
        induction w using Fin.lastCases with
        | last => simp [embed] at h
        | cast w => simpa [embed] using h
    | inr w =>
      induction v using Fin.lastCases <;> simp [embed] at h
  | inr v =>
    cases w with
    | inl w => induction w using Fin.lastCases <;> simp [embed] at h
    | inr w => simpa [embed] using h

abbrev arity {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1)))
    (a b : Fin n → Bool) {k : ℕ} : Tag P k → ℕ
  | Sum.inl c => P.arity c
  | Sum.inr p => clauseArity (a p.1) (b p.1) p.2.2

abbrev table {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1)))
    (a b : Fin n → Bool) {k : ℕ} : (c : Tag P k) → Signature AlgebraicComplex (arity P a b c)
  | Sum.inl c => P.constraint c
  | Sum.inr p => clauseTable (a p.1) (b p.1) p.2.2

abbrev scope {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1)))
    (a b : Fin n → Bool) {k : ℕ} :
    (c : Tag P k) → Fin (arity P a b c) → Fin 2 ⊕ Hidden P
  | Sum.inl c, j => embed P (P.scope c j)
  | Sum.inr p, j => clauseScope (Sum.inl 0)
      (Sum.inr (Sum.inr (Sum.inl p.1))) (Sum.inr (Sum.inr (Sum.inr p.1)))
      (a p.1) (b p.1) p.2.2 j

abbrev compile {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1)))
    (a b : Fin n → Bool) (k : ℕ) : Presentation AlgebraicComplex (Fin 2) :=
  OrderedPresentation.ordered (arity P a b (k := k)) (table P a b) (scope P a b)

theorem uses {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1)))
    (a b : Fin n → Bool) (k : ℕ) {F : SignatureFamily AlgebraicComplex}
    (hP : P.Uses F)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F) :
    (compile P a b k).Uses F := by
  apply OrderedPresentation.ordered_uses
  intro c
  cases c with
  | inl c => exact hP c
  | inr p =>
    rcases p with ⟨i,q,c⟩
    change (⟨clauseArity (a i) (b i) c,clauseTable (a i) (b i) c⟩ : AnySignature AlgebraicComplex) ∈ F
    cases ha : a i <;> cases hb : b i <;> cases c <;> assumption

theorem degree_sum {K B : Type} (P : Presentation K B)
    (v : B ⊕ Fin P.hiddenCount) :
    P.degree v = ∑ c, ∑ j, if P.scope c j = v then 1 else 0 := by
  classical
  unfold Presentation.degree
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_filter,Fintype.sum_sigma]
  rfl

theorem old_divisible {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1)))
    {k : ℕ} (hP : P.DegreeDivisible k) (v : Fin 2 ⊕ Hidden P) :
    k ∣ ∑ c, ∑ j, if embed P (P.scope c j) = v then 1 else 0 := by
  by_cases hv : ∃ w, embed P w = v
  · obtain ⟨w,rfl⟩ := hv
    have he : (∑ c, ∑ j, if embed P (P.scope c j) = embed P w then 1 else 0) =
        P.degree w := by
      calc
        _ = ∑ c, ∑ j, if P.scope c j = w then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro c _
          apply Finset.sum_congr rfl
          intro j _
          simp only [(embed_injective P).eq_iff]
        _ = P.degree w := (degree_sum P w).symm
    exact he.symm ▸ hP w
  · have hn : ∀ w, embed P w ≠ v := by simpa using hv
    simp [hn]

theorem compile_degree {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1)))
    (a b : Fin n → Bool) (k : ℕ) (w : Fin 2 ⊕ Hidden P) :
    (compile P a b k).degree (OrderedPresentation.variableEquiv w) =
      ∑ c : Tag P k, ∑ j, if scope P a b c j = w then 1 else 0 := by
  dsimp only [compile]
  convert OrderedPresentation.ordered_degree (arity P a b) (table P a b) (scope P a b) w using 1
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> rfl

theorem divisible {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1)))
    (a b : Fin n → Bool) {k : ℕ} (hP : P.DegreeDivisible k) :
    (compile P a b k).DegreeDivisible k := by
  intro v
  obtain ⟨w,rfl⟩ := (OrderedPresentation.variableEquiv (B := Fin 2) (H := Hidden P)).surjective v
  rw [compile_degree,Fintype.sum_sum_type]
  apply dvd_add
  · simpa only [scope] using old_divisible P hP w
  · simp only [Fintype.sum_prod_type]
    apply Finset.dvd_sum
    intro i _
    let d : ℕ := ∑ c : Bool, ∑ j : Fin (clauseArity (a i) (b i) c),
      if clauseScope (Sum.inl 0 : Fin 2 ⊕ Hidden P)
        (Sum.inr (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inr (Sum.inr i)))
        (a i) (b i) c j = w then 1 else 0
    have ht : k ∣ ∑ _ : Fin k, d := by
      rw [Finset.sum_const]
      simp only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      exact dvd_mul_right k d
    convert ht using 1

abbrev selected {n : ℕ} (a b : Fin n → Bool) (s : Bool) : Extra n → Bool :=
  Sum.elim (fun i => rowBit (a i) (b i) s) (fun i => auxBit (a i) (b i) s)

theorem gadget_product {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1)))
    (a b : Fin n → Bool) {k : ℕ} (hk : 0 < k) (x : Fin 2 → Bool)
    (y : Fin P.hiddenCount → Bool) (w : Extra n → Bool) :
    (∏ p : Fin n × (Fin k × Bool),
      table P a b (Sum.inr p)
        (fun j => Sum.elim x (Sum.elim y w) (scope P a b (Sum.inr p) j))) =
      if w = selected a b (x 0) then 1 else 0 := by
  have he (i : Fin n) (q : Fin k) (c : Bool) :
      table P a b (Sum.inr (i,q,c))
        (fun j => Sum.elim x (Sum.elim y w) (scope P a b (Sum.inr (i,q,c)) j)) =
      clauseTable (a i) (b i) c
        (clauseScope (x 0) (w (Sum.inl i)) (w (Sum.inr i)) (a i) (b i) c) := by
    change clauseTable (a i) (b i) c
      (fun j => Sum.elim x (Sum.elim y w)
        (clauseScope (Sum.inl 0)
          (Sum.inr (Sum.inr (Sum.inl i))) (Sum.inr (Sum.inr (Sum.inr i)))
          (a i) (b i) c j)) = _
    congr 1
    cases ha : a i <;> cases hb : b i <;> cases c <;>
      funext j <;> fin_cases j <;> rfl
  simp only [Fintype.prod_prod_type]
  simp_rw [he,clause_product]
  have hc : (Finset.univ : Finset (Fin k)).card = k := Fintype.card_fin k
  simp only [Finset.prod_const,hc]
  have hp (i : Fin n) :
      (if w (Sum.inl i) = rowBit (a i) (b i) (x 0) ∧
          w (Sum.inr i) = auxBit (a i) (b i) (x 0)
        then (1 : AlgebraicComplex) else 0) ^ k =
      if w (Sum.inl i) = rowBit (a i) (b i) (x 0) ∧
          w (Sum.inr i) = auxBit (a i) (b i) (x 0) then 1 else 0 := by
    split_ifs <;> simp [Nat.ne_of_gt hk]
  simp_rw [hp]
  rw [Fintype.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h
    funext v
    cases v with
    | inl i => exact (h i).1
    | inr i => exact (h i).2
  · intro h i
    constructor <;> exact congrFun h _

theorem old_product {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1)))
    (a b : Fin n → Bool) (x : Fin 2 → Bool) (y : Fin P.hiddenCount → Bool) :
    (∏ c : Fin P.constraints, table P a b (k := 0) (Sum.inl c)
      (fun j => Sum.elim x (Sum.elim y (selected a b (x 0)))
        (scope P a b (Sum.inl c) j))) =
    ∏ c, P.constraint c (fun j =>
      Sum.elim (Fin.snoc (if x 0 then b else a) (x 1)) y (P.scope c j)) := by
  apply Finset.prod_congr rfl
  intro c _
  congr 1
  funext j
  cases hs : P.scope c j with
  | inl i =>
    induction i using Fin.lastCases with
    | last => simp [scope,embed,hs]
    | cast i => cases hx : x 0 <;> simp [scope,embed,hs,selected,rowBit]
  | inr i => simp [scope,embed,hs]

theorem value {n : ℕ} (P : Presentation AlgebraicComplex (Fin (n + 1)))
    (a b : Fin n → Bool) {k : ℕ} (hk : 0 < k) (x : Fin 2 → Bool) :
    (compile P a b k).value x =
      P.value (Fin.snoc (if x 0 then b else a) (x 1)) := by
  rw [compile,OrderedPresentation.ordered_value]
  let e : (Hidden P → Bool) ≃ (Fin P.hiddenCount → Bool) × (Extra n → Bool) :=
    Equiv.sumArrowEquivProdArrow _ _ _
  calc
    _ = ∑ p : (Fin P.hiddenCount → Bool) × (Extra n → Bool),
        ∏ c : Tag P k, table P a b c
          (fun j => Sum.elim x (e.symm p) (scope P a b c j)) :=
      (e.symm.sum_comp (fun y : Hidden P → Bool =>
        ∏ c : Tag P k, table P a b c
          (fun j => Sum.elim x y (scope P a b c j)))).symm
    _ = P.value (Fin.snoc (if x 0 then b else a) (x 1)) := by
      rw [Fintype.sum_prod_type]
      change (∑ y : Fin P.hiddenCount → Bool, ∑ w : Extra n → Bool,
        ∏ c : Tag P k, table P a b c
          (fun j => Sum.elim x (Sum.elim y w) (scope P a b c j))) = _
      unfold Presentation.value
      refine Finset.sum_congr ?_ ?_
      · ext y
        simp only [Finset.mem_univ]
      intro y _
      simp only [Fintype.prod_sum_type]
      simp_rw [gadget_product P a b hk x y]
      rw [Finset.sum_eq_single (selected a b (x 0))]
      · simpa only [ite_true,mul_one] using old_product P a b x y
      · intro w _ hw
        simp [hw]
      · simp

theorem generated_twoRow {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    {f : Signature AlgebraicComplex (n + 1)} (hf : Generated F k f) (hk : 0 < k)
    (h0 : (⟨1,literalPin false⟩ : AnySignature AlgebraicComplex) ∈ F)
    (h1 : (⟨1,literalPin true⟩ : AnySignature AlgebraicComplex) ∈ F)
    (hX : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex) ∈ F)
    (a b : Fin n → Bool) : Generated F k (twoRow f a b) := by
  obtain ⟨P,hP,hPk,hPf⟩ := hf
  refine ⟨compile P a b k,uses P a b k hP h0 h1 hX,divisible P a b hPk,?_⟩
  funext x
  rw [value P a b hk,hPf]
  rfl


end
end Paper2.DegreeCSP.TwoRowRestriction
