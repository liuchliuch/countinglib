import Paper2.HighHeightNormalization.PairedAway
import Paper2.HighHeightNormalization.DistinctMates

/-! The complete algebraic case split after normalizing one nonzero seed card.
No final propagation condition is postulated as input. -/
namespace Paper2.HighHeightNormalization
open MatchingPropagation CommonPhase EndpointSelfLoop
variable {ι : Type}

/-- Both alternatives are proved from the actual ARS deck and one known seed.
At most two further port attachments produce one of the independently proved
Lemma 8.4 hypotheses. -/
theorem normalize_seed_alternative [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (r : PortPair ι) (hr : XAt F r) (hd : ARSDeck F) :
    (∃ z : ℂ, z ≠ 0 ∧ ∀ e, r.Disjoint e → XAt (attach r.first (binary z) F) e) ∨
    (∃ z w : ℂ, z ≠ 0 ∧ w ≠ 0 ∧
      SecondCondition (attach r.first (binary z) (attach r.second (binary w) F)) r) := by
  classical
  have hcards : ∀ e, e.Disjoint r → IsARS (contraction F e) :=
    fun e her => hd e (nonzero_of_disjoint_X F e r her hr)
  choose P z c hc hz he using hcards
  by_cases hpaired : ∀ e (her : e.Disjoint r),
      mate (P e her) (e.residual r her).first = (e.residual r her).second
  · apply Or.inl
    apply normalize_paired_away hn F r hr
    intro e her
    exact ⟨P e her,z e her,c e her,hc e her,hz e her,he e her,hpaired e her⟩
  · push Not at hpaired
    obtain ⟨s,hsr,hm⟩ := hpaired
    exact Or.inr (normalize_distinct_mates F r s hsr.symm hr (P s hsr)
      (z s hsr) (c s hsr) (hc s hsr) (hz s hsr) (he s hsr) hm)

@[simp] theorem attachFamily_one (a : ι) (z : ℂ) (F : Tensor ℂ ι) :
    attachFamily (fun _ : Fin 1 => a) (fun _ => z) F = attach a (binary z) F := rfl

@[simp] theorem attachFamily_two (a b : ι) (z w : ℂ) (F : Tensor ℂ ι) :
    attachFamily ![a,b] ![z,w] F = attach a (binary z) (attach b (binary w) F) := rfl

/-- An actual finite family of length one or two, ready for the concrete
finite-language attachment compiler. Every parameter is nonzero. -/
theorem normalize_seed_finite [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (r : PortPair ι) (hr : XAt F r) (hd : ARSDeck F) :
    ∃ (m : ℕ) (ports : Fin m → ι) (z : Fin m → ℂ),
      m ≤ 2 ∧ (∀ j, z j ≠ 0) ∧
      ((∀ e, r.Disjoint e → XAt (attachFamily ports z F) e) ∨
        SecondCondition (attachFamily ports z F) r) := by
  rcases normalize_seed_alternative hn F r hr hd with ⟨z,hz,haway⟩ | ⟨z,w,hz,hw,hs⟩
  · exact ⟨1,fun _ => r.first,fun _ => z,by omega,fun _ => hz,Or.inl haway⟩
  · refine ⟨2,![r.first,r.second],![z,w],by omega,?_,Or.inr hs⟩
    intro j
    fin_cases j
    · exact hz
    · exact hw

/-- The exact remaining terminal interface is an ARS classification of the
new actual cards, not a postulated literal-X conclusion. Once supplied for the
constructed finite attachments, Lemma 8.4 proves every scalar is nonzero. -/
theorem normalize_seed_with_deck_terminal [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (r : PortPair ι) (hr : XAt F r) (hd : ARSDeck F)
    (hterminal : ∀ {m : ℕ} (ports : Fin m → ι) (z : Fin m → ℂ),
      m ≤ 2 → (∀ j, z j ≠ 0) → ARSDeck (attachFamily ports z F)) :
    ∃ (m : ℕ) (ports : Fin m → ι) (z : Fin m → ℂ),
      m ≤ 2 ∧ (∀ j, z j ≠ 0) ∧ ∀ e, XAt (attachFamily ports z F) e := by
  obtain ⟨m,ports,z,hm,hz,hcondition⟩ := normalize_seed_finite hn F r hr hd
  exact ⟨m,ports,z,hm,hz,x_line_propagation hn _ (hterminal ports z hm hz) r hcondition⟩

end Paper2.HighHeightNormalization
