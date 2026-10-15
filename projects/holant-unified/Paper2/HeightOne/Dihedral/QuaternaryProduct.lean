import Paper2.HeightOne.Dihedral.QuaternaryDeck
import Paper2.HeightOne.PhaseCards.ProductPresentation

/-! Literal standard-Product witnesses for the one/two complementary-pair
normal forms forced by the complete odd-dihedral four-port deck. -/
namespace Paper2.HeightOne.Dihedral
open Tractable PhaseCards PhasePencil
noncomputable section

abbrev firstPorts (i : Fin 3) : Fin 2 → Fin 4 := ![0, i.succ]
abbrev secondPorts (i : Fin 3) : Fin 2 → Fin 4 := ![otherFirst i, otherSecond i]

def sectorWord (i : Fin 3) (a : Word4) (b c : Bool) : Word4 :=
  if b then (if c then flipAll a else centralWord i a)
  else (if c then flipAll (centralWord i a) else a)

lemma sector_restrict_iff (i : Fin 3) (a x : Word4) (b c : Bool) :
    ((x ∘ firstPorts i = fun j => if b then !(a (firstPorts i j)) else a (firstPorts i j)) ∧
     (x ∘ secondPorts i = fun j => if c then !(a (secondPorts i j)) else a (secondPorts i j))) ↔
      x = sectorWord i a b c := by
  fin_cases i <;> cases b <;> cases c <;>
    simp only [funext_iff, Fin.forall_fin_succ, firstPorts, secondPorts,
      otherFirst, otherSecond, Function.comp_apply, sectorWord, flipAll,
      centralWord, flipPair, Fin.succ_zero_eq_one, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_succ, Bool.false_eq_true,
      Bool.true_eq_false, ↓reduceIte, Fin.zero_eta, Fin.isValue, Bool.not_not]
  all_goals simp_all <;> tauto


lemma restricted_point_mul (i : Fin 3) (a x : Word4) (b c : Bool) :
    point (fun j : Fin 2 => if b then !(a (firstPorts i j)) else a (firstPorts i j))
      (x ∘ firstPorts i) *
    point (fun j : Fin 2 => if c then !(a (secondPorts i j)) else a (secondPorts i j))
      (x ∘ secondPorts i) = point (sectorWord i a b c) x := by
  classical
  simp only [point, ← sector_restrict_iff]
  split_ifs <;> simp_all

/-- Four independent block coordinates are combined by an actual product,
not by asserting that a sum of gadget tables is realizable. -/
def blockProduct (i : Fin 3) (a : Word4) (p r s : AlgebraicComplex) :
    Signature AlgebraicComplex 4 := fun x =>
  p * twoPoint (a ∘ firstPorts i) r (x ∘ firstPorts i) *
    twoPoint (a ∘ secondPorts i) s (x ∘ secondPorts i)

lemma blockProduct_product (i : Fin 3) (a : Word4) (p r s : AlgebraicComplex) :
    Product (blockProduct i a p r s) := by
  change Product (fun x => p * twoPoint (a ∘ firstPorts i) r (x ∘ firstPorts i) *
    twoPoint (a ∘ secondPorts i) s (x ∘ secondPorts i))
  simpa only [mul_assoc] using (((twoPoint_product (by decide : 0 < 2) (a ∘ firstPorts i) r).rename (firstPorts i)).mul
    ((twoPoint_product (by decide : 0 < 2) (a ∘ secondPorts i) s).rename (secondPorts i))).scale p

lemma blockProduct_expand (i : Fin 3) (a x : Word4) (p r s : AlgebraicComplex) :
    blockProduct i a p r s x = p * (point a x + r * point (centralWord i a) x +
      s * point (flipAll (centralWord i a)) x + r * s * point (flipAll a) x) := by
  have h00 := restricted_point_mul i a x false false
  have h10 := restricted_point_mul i a x true false
  have h01 := restricted_point_mul i a x false true
  have h11 := restricted_point_mul i a x true true
  simp only [Bool.false_eq_true, ↓reduceIte, sectorWord] at h00 h10 h01 h11
  dsimp only [blockProduct, twoPoint, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
    Function.comp_def]
  dsimp only [Function.comp_def] at h00 h10 h01 h11
  linear_combination p * h00 + (p * r) * h10 + (p * s) * h01 + (p * r * s) * h11


lemma sector_distinct (i : Fin 3) (a : Word4) :
    a ≠ flipAll a ∧ a ≠ centralWord i a ∧ a ≠ flipAll (centralWord i a) ∧
    flipAll a ≠ centralWord i a ∧ flipAll a ≠ flipAll (centralWord i a) ∧
    centralWord i a ≠ flipAll (centralWord i a) := by
  fin_cases i <;>
    simp [funext_iff, Fin.forall_fin_succ, flipAll, centralWord, flipPair]


lemma blockProduct_of_values (f : Signature AlgebraicComplex 4) (i : Fin 3) (a : Word4)
    (p r s : AlgebraicComplex) (hp : f a = p)
    (hx : f (centralWord i a) = r * p)
    (hy : f (flipAll (centralWord i a)) = s * p)
    (ht : f (flipAll a) = (r * s) * p)
    (hsupp : ∀ x, f x ≠ 0 → x = a ∨ x = flipAll a ∨
      x = centralWord i a ∨ x = flipAll (centralWord i a)) :
    f = blockProduct i a p r s := by
  classical
  obtain ⟨h01,h02,h03,h12,h13,h23⟩ := sector_distinct i a
  funext x
  rw [blockProduct_expand]
  by_cases hxa : x = a
  · subst x
    simp [point, hp, h01, h02, h03]
  by_cases hxt : x = flipAll a
  · subst x
    simp [point, ht, h01.symm, h12, h13]
    ring
  by_cases hxx : x = centralWord i a
  · subst x
    simp [point, hx, h02.symm, h12.symm, h23]
    ring
  by_cases hxy : x = flipAll (centralWord i a)
  · subst x
    simp [point, hy, h03.symm, h13.symm, h23.symm]
    ring
  have hz : f x = 0 := by
    by_contra hn
    rcases hsupp x hn with h | h | h | h <;> contradiction
  simp [point, hz, hxa, hxt, hxx, hxy]

/-- Complete coefficient-level Product conclusion for both Walsh parities;
only the actual complete RN deck and the already proved parity are premises. -/
theorem quaternary_product_of_fullDeck {N : ℕ} (hodd : Odd N)
    {f : Signature AlgebraicComplex 4} (hpar : HasParity f)
    (hdeck : FullQuaternaryDeck N f) : Product f := by
  classical
  by_cases hf : f = 0
  · rw [hf]
    exact product_zero 4
  have hex : ∃ a, f a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (funext h)
  obtain ⟨a,ha⟩ := hex
  obtain ⟨ht, ⟨r,hr,htr⟩, hsupp | ⟨i,α,β,hα,hβ,hx,hy,hti,hsupp⟩⟩ :=
    fullDeck_support_pairs hodd hpar hdeck a ha
  · have he : f = fun x => f a * twoPoint a r x := by
      funext x
      change f x = f a * (point a x + r * point (flipAll a) x)
      have hna : a ≠ flipAll a := (sector_distinct 0 a).1
      by_cases hxa : x = a
      · subst x
        simp [point, hna]
      by_cases hxt : x = flipAll a
      · subst x
        simp [point, htr, hna.symm]
        ring
      have hz : f x = 0 := by
        by_contra hn
        exact (hsupp x hn).elim hxa hxt
      simp [point, hz, hxa, hxt]
    rw [he]
    exact (twoPoint_product (by decide : 0 < 4) a r).scale (f a)
  · rw [blockProduct_of_values f i a (f a) (-α) (-β) rfl hx hy
      (by simpa using hti) hsupp]
    exact blockProduct_product i a (f a) (-α) (-β)

end
end Paper2.HeightOne.Dihedral

