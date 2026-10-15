import Paper2.HighHeightNormalization.Attachments

/-! The unconditional algebraic start of source Lemma 8.5. -/
namespace Paper2.HighHeightNormalization
open MatchingPropagation CommonPhase EndpointSelfLoop
variable {ι : Type}

/-- The complete mountain is kept as an actual coefficient table. -/
noncomputable def completeMountain (A B : ℂ) (F : Tensor ℂ ι) : Tensor ℂ ι := by
  classical
  exact fun x => (if x = (fun _ => false) then A else 0) +
    (if x = (fun _ => true) then B else 0) + F x

@[simp] theorem extend_first (e : PortPair ι)
    (x : Remaining e.first e.second → Bool) (t : Bool) :
    extendPair e.first e.second e.distinct x t e.first = t := by
  classical
  simp [extendPair,splitPorts,Sum.elim]

@[simp] theorem extend_second (e : PortPair ι)
    (x : Remaining e.first e.second → Bool) (t : Bool) :
    extendPair e.first e.second e.distinct x t e.second = !t := by
  classical
  simp [extendPair,splitPorts,Sum.elim,e.distinct.symm]

/-- HN.1: the native-X sum kills both mountain endpoints exactly. -/
theorem contraction_completeMountain (A B : ℂ) (F : Tensor ℂ ι) (e : PortPair ι) :
    contraction (completeMountain A B F) e = contraction F e := by
  classical
  funext x
  change (∑ t : Bool, completeMountain A B F (extendPair e.first e.second e.distinct x t)) = _
  have hh (t : Bool) : completeMountain A B F (extendPair e.first e.second e.distinct x t) =
      F (extendPair e.first e.second e.distinct x t) := by
    have hfalse : extendPair e.first e.second e.distinct x t ≠ (fun _ => false) := by
      intro h
      have h₁ := congrFun h e.first
      have h₂ := congrFun h e.second
      simp only [extend_first,extend_second] at h₁ h₂
      cases t <;> simp_all
    have htrue : extendPair e.first e.second e.distinct x t ≠ (fun _ => true) := by
      intro h
      have h₁ := congrFun h e.first
      have h₂ := congrFun h e.second
      simp only [extend_first,extend_second] at h₁ h₂
      cases t <;> simp_all
    simp [completeMountain,hfalse,htrue]
  simp only [hh]
  rfl

/-- Acting on the complete mountain scales its two endpoints and applies the
same explicit finite attachment sequence to its central coefficient table. -/
theorem attachFamily_completeMountain {m : ℕ} (ports : Fin m → ι) (z : Fin m → ℂ)
    (A B : ℂ) (F : Tensor ℂ ι) :
    attachFamily ports z (completeMountain A B F) =
      completeMountain ((∏ j, star (z j)) * A) ((∏ j, z j) * B)
        (attachFamily ports z F) := by
  classical
  funext x
  simp only [attachFamily_apply,completeMountain]
  by_cases h₀ : x = (fun _ => false)
  · subst x
    simp [matingWeight]
    split
    · rename_i h
      letI : IsEmpty (Fin m) := ⟨fun j => Bool.false_ne_true (congrFun h (ports j))⟩
      simp
    · ring
  · by_cases h₁ : x = (fun _ => true)
    · subst x
      simp [matingWeight,h₀]
      ring
    · simp [h₀,h₁]

/-- No nonvanishing hypothesis on the original deck is needed to get a first
nonzero contraction: the exact EO zero-loop theorem supplies it. -/
theorem exists_nonzero_contraction [Fintype ι] (hn : 3 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (heo : Tensor.ChargeLayer F 0) (hne : F ≠ 0) :
    ∃ e : PortPair ι, contraction F e ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  apply eo_zero_of_vanishing_pair_contractions (by norm_num) hn F heo
  intro a b hab
  exact h ⟨a,b,hab⟩

/-- First stage of Lemma 8.5: choose a genuinely nonzero loop, extract its
actual displayed ARS factors, and normalize it by explicit port attachments.
All disjoint pair contractions of the new tensor are proved nonzero. -/
theorem exists_normalized_seed [Fintype ι] (hn : 3 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (heo : Tensor.ChargeLayer F 0) (hne : F ≠ 0) (hd : ARSDeck F) :
    ∃ (e : PortPair ι) (P : Matching (Remaining e.first e.second))
      (z : Fin P.count → ℂ) (c : ℂ),
      c ≠ 0 ∧ (∀ j, z j ≠ 0) ∧
      contraction F e = product P z (fun j => star (z j)) c ∧
      XAt (attachFamily (fun j => (P.ports (j,false)).val) z F) e ∧
      Tensor.ChargeLayer (attachFamily (fun j => (P.ports (j,false)).val) z F) 0 ∧
      attachFamily (fun j => (P.ports (j,false)).val) z F ≠ 0 ∧
      (∀ r : PortPair ι, r.Disjoint e →
        contraction (attachFamily (fun j => (P.ports (j,false)).val) z F) r ≠ 0) := by
  obtain ⟨e,he⟩ := exists_nonzero_contraction hn F heo hne
  obtain ⟨P,z,c,hc,hz,hprod⟩ := hd e he
  have hx := normalize_selected_loop_isX F e P z c hc hz hprod
  exact ⟨e,P,z,c,hc,hz,hprod,hx,
    attachFamily_chargeLayer _ z F 0 heo,attachFamily_nonzero _ z hz F hne,
    fun r hr => nonzero_of_disjoint_X _ r e hr hx⟩

end Paper2.HighHeightNormalization
