import Paper2.Certificates.Q6Arrays
import Paper2.Certificates.Q6SafetySymmetry

/-! Generic subset-sum naturality of the actual Q6 two-copy cards.
No orbit representative or polynomial test is added as an assumption. -/
namespace Paper2.Certificates.Q6

/-- The same legal four-wire specification without the presentation-only order
of each pair of external ports. -/
def RawValidCardSpec (s : CardSpec) : Prop :=
  s.left0 ≠ s.left1 ∧ s.right0 ≠ s.right1 ∧ Function.Bijective s.wiring ∧
    (internalLeft s).image s.wiring = internalRight s

theorem ValidCardSpec.raw {s : CardSpec} (h : ValidCardSpec s) : RawValidCardSpec s :=
  ⟨ne_of_lt h.1, ne_of_lt h.2.1, h.2.2⟩

/-- Simultaneously relabel both copies and every endpoint of all four wires. -/
def relabelCard (p : Equiv.Perm Port) (s : CardSpec) : CardSpec where
  left0 := p s.left0
  left1 := p s.left1
  right0 := p s.right0
  right1 := p s.right1
  wiring x := p (s.wiring (p.symm x))

lemma card_image_univ (p : Equiv.Perm Port) : Finset.univ.image p = Finset.univ := by
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact ⟨p.symm x, p.apply_symm_apply x⟩

lemma internalLeft_relabel (p : Equiv.Perm Port) (s : CardSpec) :
    internalLeft (relabelCard p s) = (internalLeft s).image p := by
  simp only [internalLeft, relabelCard, Finset.image_sdiff _ _ p.injective,
    Finset.image_insert, Finset.image_singleton, card_image_univ]

lemma internalRight_relabel (p : Equiv.Perm Port) (s : CardSpec) :
    internalRight (relabelCard p s) = (internalRight s).image p := by
  simp only [internalRight, relabelCard, Finset.image_sdiff _ _ p.injective,
    Finset.image_insert, Finset.image_singleton, card_image_univ]

lemma selected_image (p : Equiv.Perm Port) (u v : Port) (a b : Bool) :
    selected (p u) (p v) a b = (selected u v a b).image p := by
  cases a <;> cases b <;> simp [selected]

lemma wiring_relabel_image (p : Equiv.Perm Port) (s : CardSpec) (T : PortSet) :
    (T.image p).image (relabelCard p s).wiring = (T.image s.wiring).image p := by
  simp only [Finset.image_image, relabelCard, Function.comp_def, p.symm_apply_apply]

lemma sourceSets_relabel (p : Equiv.Perm Port) (s : CardSpec) (e : Fin 6) (T : PortSet) :
    sourceSets (relabelCard p s) e (T.image p) =
      ((sourceSets s e T).1.image p, (sourceSets s e T).2.image p) := by
  simp only [sourceSets, internalRight_relabel, wiring_relabel_image,
    Finset.image_union, Finset.image_sdiff _ _ p.injective]
  simp only [relabelCard, selected_image]

lemma internalChoices_relabel (p : Equiv.Perm Port) (s : CardSpec) (e : Fin 6) :
    internalChoices (relabelCard p s) e = (internalChoices s e).image (fun T => T.image p) := by
  simp only [internalChoices, internalLeft_relabel, Finset.powerset_image]
  rw [Finset.filter_image]
  congr 1
  ext T
  simp only [Finset.mem_filter, Finset.card_image_iff.mpr p.injective.injOn]

lemma relabelCard_raw_valid (p : Equiv.Perm Port) (s : CardSpec)
    (hs : RawValidCardSpec s) : RawValidCardSpec (relabelCard p s) := by
  refine ⟨p.injective.ne hs.1, p.injective.ne hs.2.1, ?_, ?_⟩
  · exact p.bijective.comp (hs.2.2.1.comp p.symm.bijective)
  · rw [internalLeft_relabel, wiring_relabel_image, hs.2.2.2, internalRight_relabel]

variable {K : Type*} [CommRing K]

/-- Exact naturality of the displayed double-source finite sum, before the
external pairs are put back into canonical increasing order. -/
theorem twoCopyArray_relabel (p : Equiv.Perm Port) (q q' : Fin 20 → K) (t : K) (s : CardSpec)
    (hq : ∀ S : PortSet, coefficient q' (mask S) = coefficient q (mask (S.image p))) :
    twoCopyArray q' t s = twoCopyArray q t (relabelCard p s) := by
  funext e
  unfold twoCopyArray
  rw [internalChoices_relabel, Finset.sum_image]
  · congr 1
    apply Finset.sum_congr rfl
    intro T _
    simp only [sourceMasks, sourceSets_relabel, hq]
  · intro T _ U _ he
    exact (Finset.image_injective p.injective) he

end Paper2.Certificates.Q6
