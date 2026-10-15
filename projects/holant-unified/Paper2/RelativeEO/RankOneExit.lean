import Paper2.PrimeFactorization
import Paper2.Paper1Accepted.Terminals
import Paper2.ExactInput.UnconditionalTransport
import Paper2.Tractable.Downward

/-! Rank-one ordered binary exits via genuine unary prime factors and retained
language reductions. This is the singular clause of source Lemma 3.1 using the
separately accepted factor theorem, not an assumption that factors are gadgets. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem

lemma ordered_tensor_ne_zero {m n : ℕ} (u : Signature AlgebraicComplex m)
    (v : Signature AlgebraicComplex n) (hu : u ≠ 0) (hv : v ≠ 0) :
    Signature.tensor u v ≠ 0 := by
  classical
  obtain ⟨x, hx⟩ : ∃ x, u x ≠ 0 := by
    by_contra hn; push Not at hn; exact hu (funext hn)
  obtain ⟨y, hy⟩ : ∃ y, v y ≠ 0 := by
    by_contra hn; push Not at hn; exact hv (funext hn)
  intro hz
  have hh := congrFun hz (Fin.append x y)
  have ht : u x * v y = 0 := by simpa [Signature.tensor_apply] using hh
  exact mul_ne_zero hx hy ht

theorem rankOne_supplies_factors (F : Paper1FactorClosureAccepted) (L : Language)
    (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (u v : Signature AlgebraicComplex 1) (hu : u ≠ 0) (hv : v ≠ 0)
    (hB : (⟨2, Signature.tensor u v⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ N : Language, L.family ⊆ N.family ∧
      (⟨1, u⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      (⟨1, v⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧ Reduces .nativeX N L := by
  let A := TensorDecomposition.singleton u
  let B := TensorDecomposition.singleton v
  have hval : (A.append B).value = Signature.tensor u v := by
    rw [TensorDecomposition.value_append, TensorDecomposition.value_singleton, TensorDecomposition.value_singleton]
  have hpos : ∀ j, 0 < (A.append B).arity j :=
    TensorDecomposition.factors_append A B (fun n _ => 0 < n)
      (fun _ => Nat.zero_lt_one) (fun _ => Nat.zero_lt_one)
  have hprime : ∀ j, TensorPrime ((A.append B).factor j) :=
    TensorDecomposition.factors_append A B (fun _ f => TensorPrime f)
      (fun _ => unary_tensorPrime u hu) (fun _ => unary_tensorPrime v hv)
  obtain ⟨N, hLN, hfac, _, _, hNL, _⟩ := factorClosure_with_member_decomposition
    F L hpre htwo (Signature.tensor u v) hB (A.append B) hval hpos hprime
  have hU := hfac (A.appendIndexLeft B (0 : Fin 1))
  have hV := hfac (A.appendIndexRight B (0 : Fin 1))
  rw [TensorDecomposition.append_factor_left A B (0 : Fin 1)] at hU
  rw [TensorDecomposition.append_factor_right A B (0 : Fin 1)] at hV
  exact ⟨N, hLN, hU, hV, hNL⟩

theorem rankOne_binary_hard (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (L : Language) (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (hnot : ¬ Tract (kImage L))
    (u v : Signature AlgebraicComplex 1) (hu : u ≠ 0) (hv : v ≠ 0)
    (hB : (⟨2, Signature.tensor u v⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    SharpPHard .nativeX L := by
  obtain ⟨N, hLN, hU, _, hNL⟩ := rankOne_supplies_factors F L hpre htwo u v hu hv hB
  rcases U.unary_3_4 N u hu hU with ht | hh
  · exact False.elim (hnot (ht.mono_family (familyAction_mono sourceKBasis hLN)))
  · exact hh.transport_unconditional hNL

end Paper2.RelativeEO
