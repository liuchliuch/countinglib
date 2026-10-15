import Paper2.HeightOne.PhaseCards.ProductPresentation

/-! Coefficient identities of the literal standard Product presentation. -/
namespace Paper2.Tractable
noncomputable section

/-- A rectangular recombination preserves the two bits at every named port,
allowing a different swap at each port. -/
def PortRectangle {n : ℕ} (x y z w : Fin n → Bool) : Prop :=
  ∀ i, (x i = z i ∧ y i = w i) ∨ (x i = w i ∧ y i = z i)

lemma ProductFactor.rectangle {n : ℕ} (p : ProductFactor n)
    (x y z w : Fin n → Bool) (hx : p.eval x ≠ 0) (hy : p.eval y ≠ 0)
    (hz : p.eval z ≠ 0) (hw : p.eval w ≠ 0) (hrect : PortRectangle x y z w) :
    p.eval x * p.eval y = p.eval z * p.eval w := by
  cases p with
  | unary i u hu =>
    rcases hrect i with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;>
      simp only [ProductFactor.eval, hx, hy, mul_comm]
  | equality i j =>
    have hp (a : Fin n → Bool) (ha : Signature.equality (K := AlgebraicComplex) (a i) (a j) ≠ 0) :
        Signature.equality (K := AlgebraicComplex) (a i) (a j) = 1 := by
      unfold Signature.equality at *
      split_ifs at * <;> simp_all
    exact by simpa only [ProductFactor.eval, hp x hx, hp y hy, hp z hz, hp w hw]
  | disequality i j =>
    have hp (a : Fin n → Bool) (ha : Signature.disequality (K := AlgebraicComplex) (a i) (a j) ≠ 0) :
        Signature.disequality (K := AlgebraicComplex) (a i) (a j) = 1 := by
      unfold Signature.disequality at *
      split_ifs at * <;> simp_all
    exact by simpa only [ProductFactor.eval, hp x hx, hp y hy, hp z hz, hp w hw]

/-- Four supported corners of a literal Product tensor obey every coordinate
rectangle identity. Constraints may repeat and may share variables. -/
theorem Product.rectangle {n : ℕ} {f : Signature AlgebraicComplex n} (hf : Product f)
    (x y z w : Fin n → Bool) (hx : f x ≠ 0) (hy : f y ≠ 0)
    (hz : f z ≠ 0) (hw : f w ≠ 0) (hrect : PortRectangle x y z w) :
    f x * f y = f z * f w := by
  classical
  rcases hf with rfl | ⟨c, hc, ps, rfl⟩
  · exact False.elim (hx rfl)
  have hn (a : Fin n → Bool) (ha : productFormula c ps a ≠ 0) :
      ∀ p ∈ ps, p.eval a ≠ 0 := by
    have hp := (mul_ne_zero_iff.mp ha).2
    intro p hpm
    intro hz
    exact hp (List.prod_eq_zero (List.mem_map.mpr ⟨p, hpm, hz⟩))
  have hp : ∀ p ∈ ps, p.eval x * p.eval y = p.eval z * p.eval w :=
    fun p hpm => p.rectangle x y z w (hn x hx p hpm) (hn y hy p hpm)
      (hn z hz p hpm) (hn w hw p hpm) hrect
  have he : (ps.map (fun p => p.eval x)).prod * (ps.map (fun p => p.eval y)).prod =
      (ps.map (fun p => p.eval z)).prod * (ps.map (fun p => p.eval w)).prod := by
    clear hx hy hz hw hn
    induction ps with
    | nil => simp
    | cons p ps ih =>
      have hpp := hp p (by simp)
      have hi := ih (fun q hq => hp q (by simp [hq]))
      simp only [List.map_cons, List.prod_cons]
      calc
        _ = (p.eval x * p.eval y) * ((ps.map (fun q => q.eval x)).prod * (ps.map (fun q => q.eval y)).prod) := by ring
        _ = _ := by rw [hpp, hi]; ring
  dsimp only [productFormula]
  linear_combination c ^ 2 * he

end
end Paper2.Tractable
