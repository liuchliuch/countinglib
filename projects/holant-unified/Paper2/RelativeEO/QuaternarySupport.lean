import Paper2.RelativeEO.WeightedComplementaryExit
import Paper2.RelativeEO.ARSMatching

/-! A complete finite support analysis of the actual EOTract triple condition
at arity four. The enumeration is kernel reduction over all 64 subsets of the
six central words and both choices of the one common sign. -/
namespace Paper2.RelativeEO
open Paper2.Tractable

/-- The six ordered central words, in lexicographic order. -/
def sixWord (j : Fin 6) : Fin 4 → Bool :=
  ![quadWord false false true true, quadWord false true false true,
    quadWord false true true false, quadWord true false false true,
    quadWord true false true false, quadWord true true false false] j

@[simp] theorem sixWord_weight (j : Fin 6) : weight (sixWord j) = 2 := by
  fin_cases j <;> decide

/-- Exactly all central inputs, with no implicit port permutation. -/
theorem centralWord_exists (x : Fin 4 → Bool) (hx : weight x = 2) :
    ∃ j : Fin 6, sixWord j = x := by
  have heta : quadWord (x 0) (x 1) (x 2) (x 3) = x :=
    (quadWord_eq_iff x _ _ _ _).mpr ⟨rfl,rfl,rfl,rfl⟩ |>.symm
  rw [← heta] at hx ⊢
  revert hx
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;> decide

/-- A small decidable record of only the six genuine support bits. -/
def SixTriple (S : Fin 6 → Bool) (positive : Bool) : Prop :=
  ∀ a b c : Fin 6, S a = true → S b = true → S c = true →
    (∃ d : Fin 6, S d = true ∧ sixWord d = tripleXor (sixWord a) (sixWord b) (sixWord c)) ∨
      (if positive then 0 < charge (tripleXor (sixWord a) (sixWord b) (sixWord c))
       else charge (tripleXor (sixWord a) (sixWord b) (sixWord c)) < 0)

def SixFixed (S : Fin 6 → Bool) : Prop :=
  ∃ i : Fin 4, ∃ b : Bool, ∀ j : Fin 6, S j = true → sixWord j i = b

def SixComplementary (S : Fin 6 → Bool) : Prop :=
  ∃ j : Fin 6, ∀ k : Fin 6,
    S k = true ↔ sixWord k = sixWord j ∨ sixWord k = (fun i => !(sixWord j i))

/-- The three perfect matchings each omit exactly one complementary pair. -/
def SixMatching (S : Fin 6 → Bool) : Prop :=
  ∃ j : Fin 3, ∀ k : Fin 6, S k = true ↔ k.val ≠ j.val ∧ k.val ≠ 5-j.val

instance (S : Fin 6 → Bool) (p : Bool) : Decidable (SixTriple S p) := by
  unfold SixTriple
  infer_instance
instance (S : Fin 6 → Bool) : Decidable (SixFixed S) := by
  unfold SixFixed
  infer_instance
instance (S : Fin 6 → Bool) : Decidable (SixComplementary S) := by
  unfold SixComplementary
  infer_instance
instance (S : Fin 6 → Bool) : Decidable (SixMatching S) := by
  unfold SixMatching
  infer_instance

def sixDual (j : Fin 6) : Fin 6 := ⟨5-j.val,by omega⟩

@[simp] theorem sixWord_dual (j : Fin 6) :
    sixWord (sixDual j) = fun i => !(sixWord j i) := by
  fin_cases j <;> funext i <;> fin_cases i <;> rfl

theorem sixWord_injective : Function.Injective sixWord := by
  intro a b h
  have hh : ∀ i, sixWord a i = sixWord b i := congrFun h
  revert hh
  fin_cases a <;> fin_cases b <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Complete 64-mask classification after the two analytic consequences of
EOTract. The proof uses kernel reduction, with no native evaluator axiom. -/
theorem six_mask_classification : ∀ S : Fin 6 → Bool,
    ((∃ j, S j = true ∧ S (sixDual j) = true) →
      ∀ k, S k = true → S (sixDual k) = true) →
    (¬ ∀ k, S k = true) → SixFixed S ∨ SixComplementary S ∨ SixMatching S := by
  decide +kernel

/-- The triple condition forces complementary support closure as soon as
one complementary pair is present, and forbids all six entries at once. -/
theorem six_support_classification (S : Fin 6 → Bool) (positive : Bool)
    (ht : SixTriple S positive) : SixFixed S ∨ SixComplementary S ∨ SixMatching S := by
  apply six_mask_classification S
  · rintro ⟨a,ha,ha'⟩ k hk
    have he : tripleXor (sixWord a) (sixWord (sixDual a)) (sixWord k) = sixWord (sixDual k) := by
      rw [sixWord_dual,sixWord_dual]
      funext i
      cases ha : sixWord a i <;> cases hk : sixWord k i <;> simp [tripleXor,ha,hk]
    rcases ht a (sixDual a) k ha ha' hk with ⟨d,hd,heq⟩ | hbad
    · rw [he] at heq
      exact sixWord_injective heq ▸ hd
    · have hz : charge (sixWord (sixDual k)) = 0 := by
        unfold charge
        rw [sixWord_weight]
        norm_num
      rw [he,hz] at hbad
      cases positive <;> simp_all
  · intro hall
    have hn := ht 0 1 2 (hall _) (hall _) (hall _)
    have hp := ht 3 4 5 (hall _) (hall _) (hall _)
    have he0 : tripleXor (sixWord 0) (sixWord 1) (sixWord 2) = (fun _ => false) := by decide
    have he1 : tripleXor (sixWord 3) (sixWord 4) (sixWord 5) = (fun _ => true) := by decide
    rw [he0] at hn
    rw [he1] at hp
    have hno (v : Bool) : ¬ ∃ d, S d = true ∧ sixWord d = (fun _ => v) := by
      rintro ⟨d,_,hd⟩
      have hw := sixWord_weight d
      rw [hd] at hw
      cases v <;> norm_num [weight] at hw
    have hn' := hn.resolve_left (hno false)
    have hp' := hp.resolve_left (hno true)
    cases positive
    · norm_num [charge,weight] at hp'
    · norm_num [charge,weight] at hn'

/-- Actual EOTract gives the finite triple condition on the exact support mask. -/
theorem eoTract_sixTriple (F : SignatureFamily AlgebraicComplex)
    (h : EOTract F) (f : Signature AlgebraicComplex 4)
    (hmem : (⟨4,f⟩ : AnySignature AlgebraicComplex) ∈ F) :
    ∃ positive : Bool, SixTriple (fun j => decide (f (sixWord j) ≠ 0)) positive := by
  classical
  obtain ⟨_,hEO,sign,C,ht,_⟩ := h
  have hs := ht ⟨4,f⟩ hmem
  have heo := (hEO ⟨4,f⟩ hmem).2
  let positive : Bool := match sign with | .positive => true | .negative => false
  refine ⟨positive,?_⟩
  intro a b c ha hb hc
  simp only [decide_eq_true_eq] at ha hb hc
  rcases hs (sixWord a) (sixWord b) (sixWord c) ha hb hc with hd | hd
  · left
    have hw : weight (tripleXor (sixWord a) (sixWord b) (sixWord c)) = 2 := by
      by_contra hn
      apply hd
      apply heo
      change 2 * weight _ ≠ 4
      omega
    obtain ⟨d,he⟩ := centralWord_exists _ hw
    refine ⟨d,by simpa only [decide_eq_true_eq,he] using hd,he⟩
  · right
    cases sign <;> simp_all [positive,EOSign.value]

end Paper2.RelativeEO
