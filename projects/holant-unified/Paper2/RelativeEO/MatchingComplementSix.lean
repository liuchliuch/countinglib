import Paper2.RelativeEO.MatchingComplement
import Mathlib.Tactic

/-! Exhaustive literal four-port matching support, without any Q6 certificate
or EO terminal import. The finite theorem enumerates only four-port bijections. -/
namespace Paper2.RelativeEO.MatchingComplement
open scoped BigOperators
variable {K : Type*} [CommRing K] [IsDomain K]

def sixWord (j : Fin 6) : Fin 4 → Bool :=
  ![![false,false,true,true], ![false,true,false,true], ![false,true,true,false],
    ![true,false,false,true], ![true,false,true,false], ![true,true,false,false]] j

def pairTest (e : Fin 2 × Bool → Fin 4) (x : Fin 4 → Bool) : Prop :=
  ∀ i, x (e (i,true)) = !(x (e (i,false)))

lemma four_port_matching_exhaustive (e : Fin 2 × Bool → Fin 4) (he : Function.Injective e) :
    ∃ k : Fin 3, ∀ j : Fin 6, pairTest e (sixWord j) ↔ j.val ≠ k.val ∧ j.val ≠ 5 - k.val := by
  have h01 := he.ne (show (0,false) ≠ (0,true) by decide)
  have h02 := he.ne (show (0,false) ≠ (1,false) by decide)
  have h03 := he.ne (show (0,false) ≠ (1,true) by decide)
  have h12 := he.ne (show (0,true) ≠ (1,false) by decide)
  have h13 := he.ne (show (0,true) ≠ (1,true) by decide)
  have h23 := he.ne (show (1,false) ≠ (1,true) by decide)
  generalize ha : e (0,false) = a at *
  generalize hb : e (0,true) = b at *
  generalize hc : e (1,false) = c at *
  generalize hd : e (1,true) = d at *
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> try contradiction
  all_goals simp [Fin.exists_fin_succ,Fin.forall_fin_succ,pairTest,ha,hb,hc,hd,sixWord]

theorem six_support_pattern {f : Signature K 4} (hf : WeightedMatching.IsProduct f) :
    ∃ k : Fin 3, ∀ j : Fin 6,
      f (sixWord j) ≠ 0 ↔ j.val ≠ k.val ∧ j.val ≠ 5 - k.val := by
  obtain ⟨P,p,q,c,hc,rfl⟩ := hf
  have hp : P.count = 2 := by have := Matching.pair_count P; omega
  rcases P with ⟨count,ports⟩
  change count = 2 at hp
  subst count
  obtain ⟨k,hk⟩ := four_port_matching_exhaustive ports ports.injective
  refine ⟨k,fun j => ?_⟩
  rw [WeightedMatching.product_ne_zero _ _ _ _ hc]
  exact hk j

lemma sixWord_complement (j : Fin 6) :
    sixWord (⟨5-j.val,by omega⟩ : Fin 6) = fun k => !(sixWord j k) := by
  fin_cases j <;> decide

theorem quaternary_matching_three_cases {f : Signature K 4}
    (hf : WeightedMatching.IsProduct f) :
    (f (sixWord 0) = 0 ∧ f (sixWord 5) = 0 ∧
      f (sixWord 1) ≠ 0 ∧ f (sixWord 4) ≠ 0 ∧
      f (sixWord 2) ≠ 0 ∧ f (sixWord 3) ≠ 0 ∧
      f (sixWord 1) * f (sixWord 4) = f (sixWord 2) * f (sixWord 3)) ∨
    (f (sixWord 1) = 0 ∧ f (sixWord 4) = 0 ∧
      f (sixWord 0) ≠ 0 ∧ f (sixWord 5) ≠ 0 ∧
      f (sixWord 2) ≠ 0 ∧ f (sixWord 3) ≠ 0 ∧
      f (sixWord 0) * f (sixWord 5) = f (sixWord 2) * f (sixWord 3)) ∨
    (f (sixWord 2) = 0 ∧ f (sixWord 3) = 0 ∧
      f (sixWord 0) ≠ 0 ∧ f (sixWord 5) ≠ 0 ∧
      f (sixWord 1) ≠ 0 ∧ f (sixWord 4) ≠ 0 ∧
      f (sixWord 0) * f (sixWord 5) = f (sixWord 1) * f (sixWord 4)) := by
  obtain ⟨k,hk⟩ := six_support_pattern hf
  have hh (i j : Fin 6) (hi : f (sixWord i) ≠ 0) (hj : f (sixWord j) ≠ 0) :=
    equal_supported_complement_products hf (sixWord i) (sixWord j) hi hj
  have h0 := hk 0
  have h1 := hk 1
  have h2 := hk 2
  have h3 := hk 3
  have h4 := hk 4
  have h5 := hk 5
  fin_cases k
  · simp only [Fin.val_zero,Fin.val_one,Fin.val_ofNat] at h0 h1 h2 h3 h4 h5
    norm_num at h0 h1 h2 h3 h4 h5
    refine Or.inl ⟨h0,h5,h1,h4,h2,h3,?_⟩
    simpa [← sixWord_complement] using hh 1 2 h1 h2
  · norm_num at h0 h1 h2 h3 h4 h5
    refine Or.inr (Or.inl ⟨h1,h4,h0,h5,h2,h3,?_⟩)
    simpa [← sixWord_complement] using hh 0 2 h0 h2
  · norm_num at h0 h1 h2 h3 h4 h5
    refine Or.inr (Or.inr ⟨h2,h3,h0,h5,h1,h4,?_⟩)
    simpa [← sixWord_complement] using hh 0 1 h0 h1

end Paper2.RelativeEO.MatchingComplement

