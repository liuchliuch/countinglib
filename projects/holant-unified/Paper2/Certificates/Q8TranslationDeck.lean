import Paper2.Certificates.Q8Support
import Paper2.Certificates.RMReindex

/-! The actual translation-matching contraction deck implies Q8.19a, including
the complete two-extension sum and the exact support condition Q8.19. -/
namespace Paper2.Certificates.Q8
open ReedMuller

/-- The six surviving bits, in the previously verified affine pair order. -/
def residualWord (p q : Fin 8) (x : Word) : Fin 6 → Bool :=
  fun i => x (pairOrder p q i.succ.succ)

def pairExtension (p q : Fin 8) (a b : Bool) (y : Fin 6 → Bool) : Word :=
  fun t => (Fin.cons a (Fin.cons b y) : Word) (pairOrderInv p q t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pair_order_residual_ne (p q : Fin 8) (hpq : p ≠ q) (i : Fin 6) :
    pairOrder p q i.succ.succ ≠ p ∧ pairOrder p q i.succ.succ ≠ q := by
  revert p q i
  decide +kernel

theorem pairExtension_reconstruct (p q : Fin 8) (hpq : p ≠ q) (x : Word) :
    pairExtension p q (x p) (x q) (residualWord p q x) = x := by
  have he : (Fin.cons (x p) (Fin.cons (x q) (residualWord p q x)) : Word) =
      fun i => x (pairOrder p q i) := by
    funext i
    fin_cases i
    · change x p = x (pairOrder p q 0)
      rw [(pair_order_endpoints p q hpq).1]
    · change x q = x (pairOrder p q 1)
      rw [(pair_order_endpoints p q hpq).2]
    all_goals rfl
  funext t
  change (Fin.cons (x p) (Fin.cons (x q) (residualWord p q x)) : Word) (pairOrderInv p q t) = x t
  rw [he]
  simp only [pair_order_right_inverse]

theorem crossing_extensions (p q : Fin 8) (x : Word)
    (hp : x p = true) (hq : x q = false) :
    pairExtension p q true false (residualWord p q x) = x ∧
    pairExtension p q false true (residualWord p q x) = swap x p q := by
  have hpq : p ≠ q := by
    intro he
    exact Bool.noConfusion (hp.symm.trans (he.symm ▸ hq))
  constructor
  · simpa only [hp,hq] using pairExtension_reconstruct p q hpq x
  · have hr : residualWord p q (swap x p q) = residualWord p q x := by
      funext i
      simp only [residualWord,swap,(pair_order_residual_ne p q hpq i).1,
        (pair_order_residual_ne p q hpq i).2,ite_false]
    have he := pairExtension_reconstruct p q hpq (swap x p q)
    rw [hr] at he
    simpa only [swap,ite_true,Ne.symm hpq,ite_false] using he

/-- One endpoint of every surviving translation pair is selected. -/
def TranslationTransversal (y : Fin 6 → Bool) : Prop :=
  y 0 ≠ y 1 ∧ y 2 ≠ y 3 ∧ y 4 ≠ y 5

instance (y : Fin 6 → Bool) : Decidable (TranslationTransversal y) :=
  inferInstanceAs (Decidable (y 0 ≠ y 1 ∧ y 2 ≠ y 3 ∧ y 4 ≠ y 5))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Q8.19, with an actual word on the six surviving ports. -/
theorem translation_transversal_iff (p q : Fin 8) (x : Word)
    (hw : weight x = 4) (hp : x p = true) (hq : x q = false) :
    TranslationTransversal (residualWord p q x) ↔
      supportXor x = (fun _ => false) ∨ supportXor x = direction p q := by
  revert p q x
  decide +kernel

variable {K : Type*} [CommRing K]

theorem bellTriple_x_indicator (y : Fin 6 → Bool) :
    bellTriple (K := K) true false y = if TranslationTransversal y then 1 else 0 := by
  change Bell.X (y 0) (y 1) * Bell.X (y 2) (y 3) * Bell.X (y 4) (y 5) = _
  rw [Bell.X_eq_disequality]
  by_cases h01 : y 0 = y 1 <;> by_cases h23 : y 2 = y 3 <;> by_cases h45 : y 4 = y 5 <;>
    simp [Signature.disequality,TranslationTransversal,h01,h23,h45]

/-- The actual native-X contraction has exactly the two expected extensions. -/
theorem contractAtPair_x_crossing (f : Signature K 8) (p q : Fin 8) (x : Word)
    (hp : x p = true) (hq : x q = false) :
    contractAtPair Bell.X p q f (residualWord p q x) = f x + f (swap x p q) := by
  rw [contractAtPair,Bell.X_eq_disequality,Signature.contract_disequality]
  change f (pairExtension p q false true (residualWord p q x)) +
    f (pairExtension p q true false (residualWord p q x)) = _
  rw [(crossing_extensions p q x hp hq).1,(crossing_extensions p q x hp hq).2]
  exact add_comm _ _

/-- Precisely the nonweighted X-products on the three translation pairs.
The existing `pair_order_translation` theorem verifies their geometric labels. -/
def TranslationDeck (f : Signature K 8) (lam : Fin 8 → Fin 8 → K) : Prop :=
  ∀ p q, p ≠ q → contractAtPair Bell.X p q f =
    fun y => lam p q * bellTriple true false y

theorem TranslationDeck.swap_system (f : Signature K 8) (lam : Fin 8 → Fin 8 → K)
    (h : TranslationDeck f lam) : SwapSystem f lam := by
  intro x p q hw hp hq
  have hpq : p ≠ q := by
    intro he
    have hb : true = false := hp.symm.trans (he.symm ▸ hq)
    exact Bool.noConfusion hb
  have he := congrFun (h p q hpq) (residualWord p q x)
  rw [contractAtPair_x_crossing f p q x hp hq,bellTriple_x_indicator] at he
  simpa only [translation_transversal_iff p q x hw hp hq,mul_ite,mul_one,mul_zero] using he

/-- A specified crossing plane, transported from the even canonical ports. -/
def crossingPlane (p q : Fin 8) : Word :=
  fun t => fromMask 85 (pairOrderInv p q t)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem crossingPlane_valid (p q : Fin 8) (h : p ≠ q) :
    weight (crossingPlane p q) = 4 ∧
    supportXor (crossingPlane p q) = (fun _ => false) ∧
    crossingPlane p q p = true ∧ crossingPlane p q q = false ∧
    weight (swap (crossingPlane p q) p q) = 4 ∧
    swap (crossingPlane p q) p q q = true ∧
    swap (crossingPlane p q) p q p = false ∧
    supportXor (swap (crossingPlane p q) p q) = direction q p ∧
    swap (swap (crossingPlane p q) p q) q p = crossingPlane p q := by
  revert p q
  decide +kernel

/-- The unordered-pair symmetry of the scale follows from the actual deck. -/
theorem TranslationDeck.scales_symmetric (f : Signature K 8) (lam : Fin 8 → Fin 8 → K)
    (h : TranslationDeck f lam) : ∀ p q, lam p q = lam q p := by
  intro p q
  by_cases hpq : p = q
  · subst q
    rfl
  · have hs := TranslationDeck.swap_system f lam h
    obtain ⟨hw,hxor,hp,hq,hws,hqs,hps,hxors,hinv⟩ := crossingPlane_valid p q hpq
    have he := hs (crossingPlane p q) p q hw hp hq
    have he' := hs (swap (crossingPlane p q) p q) q p hws hqs hps
    simp only [hxor,true_or,ite_true] at he
    simp only [hxors,or_true,ite_true,hinv] at he'
    exact he.symm.trans ((add_comm _ _).trans he')

/-- Tensor-level Lemma 8.10 from the actual normalized translation deck. -/
theorem scalar_central_of_translation_deck [NoZeroDivisors K] [CharZero K]
    (f : Signature K 8) (lam : Fin 8 → Fin 8 → K)
    (h : TranslationDeck f lam) (hnz : ∀ p q, p ≠ q → lam p q ≠ 0)
    (heo : ∀ x, weight x ≠ 4 → f x = 0) :
    ∃ c : K, c ≠ 0 ∧ f = fun x => c * central x :=
  scalar_central_of_swap_system f lam (TranslationDeck.swap_system f lam h) (TranslationDeck.scales_symmetric f lam h) hnz heo

end Paper2.Certificates.Q8
