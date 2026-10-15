import Paper2.DegreeCSP.EqualityTemplates

/-! The deterministic equality template at the literal input degree. The
divisibility proof transports only the boundary arity; vertex order, internal
edge order, and every local port ordinal are unchanged. -/
namespace Paper2.DegreeCSP.EqualityDegreeTemplates
open Paper2.Tractable Paper2.ExactInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

def make (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d) : Network AlgebraicComplex d :=
  if h0 : d=0 then
    (EqualityTemplates.nullary k).reindexBoundary (finCongr h0.symm)
  else
    (EqualityTemplates.positive (d/k) k hk).reindexBoundary (finCongr (Nat.div_mul_cancel hd))

private theorem reindexBoundary_refl {n : ℕ} (N : Network AlgebraicComplex n) :
    N.reindexBoundary (Equiv.refl _) = N := by
  rcases N with ⟨S,f,E⟩
  have hp : S.ports.trans (Equiv.sumCongr (Equiv.refl _) (Equiv.refl _)) = S.ports := by
    ext p
    change Sum.map id id (S.ports p) = S.ports p
    cases S.ports p <;> rfl
  dsimp only [Network.reindexBoundary]
  rw [hp]

theorem make_zero (k : ℕ) (hk : 3 ≤ k) (hd : k ∣ 0) :
    make k hk 0 hd = EqualityTemplates.nullary k := by
  simp only [make,dite_true]
  change (EqualityTemplates.nullary k).reindexBoundary (Equiv.refl _) = _
  exact reindexBoundary_refl _

theorem make_positive (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d) (h0 : d ≠ 0) :
    make k hk d hd =
      (EqualityTemplates.positive (d/k) k hk).reindexBoundary (finCongr (Nat.div_mul_cancel hd)) :=
  dite_eq_right h0

theorem multiplicity_positive (k : ℕ) (_hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d) (h0 : d ≠ 0) :
    0 < d/k := by
  have he := Nat.div_mul_cancel hd
  by_contra h
  have hz : d/k=0 := Nat.eq_zero_of_not_pos h
  rw [hz,zero_mul] at he
  exact h0 he.symm

theorem make_vertices (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d) :
    (make k hk d hd).shape.vertices = if d=0 then 2 else 3*(d/k)-2 := by
  by_cases h0 : d=0
  · simp [make,h0,Network.reindexBoundary,EqualityTemplates.nullary]
  · rw [make_positive k hk d hd h0,ite_eq_right h0]
    exact EqualityTemplates.positive_vertices_linear _ _ hk (multiplicity_positive k hk d hd h0)

theorem make_edges (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d) :
    (make k hk d hd).shape.edges = if d=0 then k else (d/k-1)*k := by
  by_cases h0 : d=0 <;>
    simp [make,h0,Network.reindexBoundary,EqualityTemplates.nullary,EqualityTemplates.positive]

theorem make_arity (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d)
    (v : Fin (make k hk d hd).shape.vertices) : (make k hk d hd).shape.arity v = k := by
  cases d <;> rfl

theorem make_vertex (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d)
    (v : Fin (make k hk d hd).shape.vertices) :
    (⟨(make k hk d hd).shape.arity v,(make k hk d hd).vertex v⟩ : AnySignature AlgebraicComplex) =
      ⟨k,equality k⟩ := by
  cases d <;> rfl

theorem make_nativeX (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d) :
    (make k hk d hd).NativeX := by
  unfold make
  split_ifs
  · exact (EqualityTemplates.nullary_nativeX k).reindexBoundary _
  · exact (EqualityTemplates.positive_nativeX _ _ hk).reindexBoundary _

theorem make_uses (F : SignatureFamily AlgebraicComplex)
    (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d)
    (heq : (⟨k,equality k⟩ : AnySignature AlgebraicComplex) ∈ F) :
    (make k hk d hd).Uses F := by
  intro v
  rw [make_vertex]
  exact heq

end
end Paper2.DegreeCSP.EqualityDegreeTemplates
