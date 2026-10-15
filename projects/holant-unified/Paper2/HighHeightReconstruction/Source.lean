import Paper2.HighHeightReconstruction.RestoreEdge
import Paper2.HighHeightReconstruction.Triangle
import Paper2.HighHeightReconstruction.CommonEdge

/-!
# Paper 2 Lemma 8.7: matching-product reconstruction

Both source alternatives are proved from actual finite sums, matching support,
finite port selection, and EO subdeck injectivity. No Shao–Cai theorem is added
as an axiom or accepted input. The argument proves the stronger complex-scalar
version and therefore does not require the separate ARS/real-scalar premises.
-/
namespace Paper2.HighHeightReconstruction
open CommonPhase EndpointSelfLoop MatchingPropagation
variable {ι : Type}

/-- The eight-port overlap clause, valid also at larger arities. The shared
edge is recovered as an actual X factor on its original named ports. -/
theorem reconstruct_of_shared_overlap [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hF : Tensor.ChargeLayer F 0)
    (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ r, lam r ≠ 0)
    (r s e : PortPair ι) (hrs : ¬SamePair r s) (hover : ¬r.Disjoint s)
    (hre : r.Disjoint e) (hse : s.Disjoint e)
    (hr : EdgeIn P r e hre) (hs : EdgeIn P s e hse) :
    IsX F ∧ F = project e F := by
  classical
  have hroom : (pairPorts e ∪ (pairPorts r ∪ pairPorts s)).card + 3 ≤ Fintype.card ι := by
    have h₁ := pairPorts_union_le_three r s hover
    have h₂ := Finset.card_union_le (pairPorts e) (pairPorts r ∪ pairPorts s)
    simp only [card_pairPorts] at h₂
    omega
  have hp := edge_persistent_of_two hn F lam P hd hnz r s e hrs hre hse hr hs hroom
  exact ⟨isX_of_persistent_edge hn F hF lam P hd hnz e hp,
    persistent_edge_factor hn F hF lam P hd e hp⟩

/-- At arity at least ten, two disjoint cards necessarily share an edge. There
is room for a fresh triangle, so that edge reconstructs the entire tensor. -/
theorem reconstruct_ge_ten [Fintype ι] (hn : 10 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hF : Tensor.ChargeLayer F 0)
    (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ r, lam r ≠ 0) : IsX F := by
  classical
  obtain ⟨a,b,hab⟩ := Fintype.one_lt_card_iff.mp (by omega : 1 < Fintype.card ι)
  let r : PortPair ι := ⟨a,b,hab⟩
  obtain ⟨s,e,hrs,hre,hse,hr,hs⟩ := exists_shared_edge (by omega) F lam P hd hnz r
  have hroom : (pairPorts e ∪ (pairPorts r ∪ pairPorts s)).card + 3 ≤ Fintype.card ι := by
    have h₁ := Finset.card_union_le (pairPorts r) (pairPorts s)
    have h₂ := Finset.card_union_le (pairPorts e) (pairPorts r ∪ pairPorts s)
    simp only [card_pairPorts] at h₁ h₂
    omega
  have hp := edge_persistent_of_two (by omega) F lam P hd hnz r s e
    (not_same_of_disjoint r s hrs) hre hse hr hs hroom
  exact isX_of_persistent_edge (by omega) F hF lam P hd hnz e hp

/-- Literal n≥10 source wrapper: exact ARS, even arity, and nonzero real deck
coefficients are accepted explicitly and imply the claimed matching product. -/
theorem shao_cai_ge_ten_source [Fintype ι] (hn : 10 ≤ Fintype.card ι)
    (_heven : Even (Fintype.card ι)) (G : Tensor ℂ ι)
    (hG : Tensor.ChargeLayer G 0)
    (_hARS : ∀ x, star (G (fun i => !(x i))) = G x)
    (mu : PortPair ι → ℝ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck G (fun r => (mu r : ℂ)) P) (hnz : ∀ r, mu r ≠ 0) : IsX G :=
  reconstruct_ge_ten hn G hG _ P hd (fun r => by exact_mod_cast hnz r)

/-- The exact n=8 source clause additionally retains the actual shared X
factor's coefficient formula, rather than merely asserting a product exists. -/
theorem shao_cai_eight_source [Fintype ι] (hn : Fintype.card ι = 8)
    (G : Tensor ℂ ι) (hG : Tensor.ChargeLayer G 0)
    (_hARS : ∀ x, star (G (fun i => !(x i))) = G x)
    (mu : PortPair ι → ℝ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck G (fun r => (mu r : ℂ)) P) (hnz : ∀ r, mu r ≠ 0)
    (r s e : PortPair ι) (hrs : ¬SamePair r s) (hover : ¬r.Disjoint s)
    (hre : r.Disjoint e) (hse : s.Disjoint e)
    (hr : EdgeIn P r e hre) (hs : EdgeIn P s e hse) :
    IsX G ∧ ∀ x, G x = Signature.disequality (x e.first) (x e.second) *
      (contraction G e (restrict e.first e.second x) / 2) := by
  obtain ⟨hX,hproj⟩ := reconstruct_of_shared_overlap (by omega) G hG _ P hd
    (fun r => by exact_mod_cast hnz r) r s e hrs hover hre hse hr hs
  refine ⟨hX,?_⟩
  intro x
  rw [congrFun hproj x]
  unfold project
  rw [PortPair.pairSum_eq_loop]
  ring

/-- High arity needs no additional oracle after the proved 8.4 alternatives. -/
theorem propagation_reconstructs_ge_ten [Fintype ι] (hn : 10 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hF : Tensor.ChargeLayer F 0) (hd : ARSDeck F)
    (r : PortPair ι) (h : (∀ e, r.Disjoint e → XAt F e) ∨ SecondCondition F r) :
    IsX F := by
  obtain ⟨lam,P,hdeck,hnz⟩ := x_line_matching_deck (by omega) F hd r h
  exact reconstruct_ge_ten hn F hF lam P hdeck hnz

/-- An algebraic input's reconstructed scalar is an actual input coefficient
at a transversal word, hence belongs to the original algebraic field. -/
theorem algebraic_matching_scalar (F : Tensor Tractable.AlgebraicComplex ι)
    (h : IsX (fun x => (F x : ℂ))) :
    ∃ (P : Matching ι) (c : Tractable.AlgebraicComplex), c ≠ 0 ∧
      ∀ x, (F x : ℂ) = (c : ℂ) * literal P ℂ x := by
  obtain ⟨P,c,hc,he⟩ := h
  let x₀ := word P (fun _ => false)
  have hval : (F x₀ : ℂ) = c := by
    have hh := congrFun he x₀
    simpa only [x₀,literal_word,mul_one] using hh
  refine ⟨P,F x₀,?_,?_⟩
  · intro hz
    have hh : (F x₀ : ℂ) = 0 := by rw [hz]; rfl
    exact hc (hval.symm.trans hh)
  · intro x
    rw [hval]
    exact congrFun he x

/-- The high-arity reconstruction keeps its scalar inside the algebraic
coefficient field of the input rather than enlarging that field. -/
theorem reconstruct_algebraic_ge_ten [Fintype ι] (hn : 10 ≤ Fintype.card ι)
    (F : Tensor Tractable.AlgebraicComplex ι) (hF : Tensor.ChargeLayer F 0)
    (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck (fun x => (F x : ℂ)) lam P) (hnz : ∀ r, lam r ≠ 0) :
    ∃ (Q : Matching ι) (c : Tractable.AlgebraicComplex), c ≠ 0 ∧
      ∀ x, (F x : ℂ) = (c : ℂ) * literal Q ℂ x := by
  apply algebraic_matching_scalar F
  apply reconstruct_ge_ten hn (fun x => (F x : ℂ)) _ lam P hd hnz
  intro x hx
  apply hF x
  intro hz
  apply hx
  change (F x : ℂ) = 0
  rw [hz]
  rfl

end Paper2.HighHeightReconstruction
