import Paper2.MatchingPropagation.Surviving

namespace Paper2.MatchingPropagation
open CommonPhase EndpointSelfLoop
variable {ι : Type}

/-- Pair contraction on the actual surviving port subtype. -/
noncomputable abbrev contraction (F : Tensor ℂ ι) (e : PortPair ι) :=
  loop e.first e.second e.distinct F

def XAt (F : Tensor ℂ ι) (e : PortPair ι) : Prop := IsX (contraction F e)

def WeightedDeck (F : Tensor ℂ ι) : Prop :=
  ∀ e : PortPair ι, contraction F e ≠ 0 → IsWeighted (contraction F e)

def ARSDeck (F : Tensor ℂ ι) : Prop :=
  ∀ e : PortPair ι, contraction F e ≠ 0 → IsARS (contraction F e)

theorem ARSDeck.weighted {F : Tensor ℂ ι} (h : ARSDeck F) : WeightedDeck F :=
  fun e he => (h e he).weighted

theorem pairSum_isX_nonzero (e : PortPair ι) {F : Tensor ℂ ι} (h : IsX F) :
    ∃ x, e.pairSum F x ≠ 0 := by
  obtain ⟨P,c,hc,rfl⟩ := h
  obtain ⟨y,hy⟩ := exists_loop_literal_ne_zero P e.first e.second e.distinct
  refine ⟨extendPair e.first e.second e.distinct y false, ?_⟩
  rw [PortPair.pairSum_mul]
  change c * e.pairSum (literal P ℂ) _ ≠ 0
  rw [PortPair.pairSum_eq_loop, PortPair.restrict_extend]
  exact mul_ne_zero hc hy

/-- Both double-loop orders, compared on exactly the same original assignment. -/
theorem double_loop_eq (F : Tensor ℂ ι) (e r : PortPair ι) (h : e.Disjoint r)
    (x : ι → Bool) :
    (e.residual r h).pairSum (contraction F e) (restrict e.first e.second x) =
      (r.residual e h.symm).pairSum (contraction F r) (restrict r.first r.second x) := by
  rw [← PortPair.pairSum_lift e r h, ← PortPair.pairSum_lift r e h.symm]
  have he : (fun y => contraction F e (restrict e.first e.second y)) = e.pairSum F := by
    funext y
    exact (PortPair.pairSum_eq_loop e F y).symm
  have hr : (fun y => contraction F r (restrict r.first r.second y)) = r.pairSum F := by
    funext y
    exact (PortPair.pairSum_eq_loop r F y).symm
  rw [he,hr,PortPair.pairSum_comm h]

/-- HN.4, including the nonvanishing that cannot be assumed in the source deck. -/
theorem double_comparison (F : Tensor ℂ ι) (e r : PortPair ι) (h : e.Disjoint r)
    (hr : XAt F r) :
    (∃ x, (e.residual r h).pairSum (contraction F e) x ≠ 0) ∧
      Flat ((e.residual r h).pairSum (contraction F e)) := by
  have hnz := pairSum_isX_nonzero (r.residual e h.symm) hr
  have hflat := pairSum_isX_flat (r.residual e h.symm) hr
  constructor
  · obtain ⟨y,hy⟩ := hnz
    let x := extendPair r.first r.second r.distinct y false
    refine ⟨restrict e.first e.second x, ?_⟩
    rw [double_loop_eq F e r h]
    simpa only [x,PortPair.restrict_extend] using hy
  · intro x y hx hy
    let X := extendPair e.first e.second e.distinct x false
    let Y := extendPair e.first e.second e.distinct y false
    have hX := double_loop_eq F e r h X
    have hY := double_loop_eq F e r h Y
    simp only [X,Y,PortPair.restrict_extend] at hX hY
    rw [hX] at hx
    rw [hY] at hy
    rw [hX,hY]
    exact hflat _ _ hx hy

theorem nonzero_of_disjoint_X (F : Tensor ℂ ι) (e r : PortPair ι)
    (h : e.Disjoint r) (hr : XAt F r) : contraction F e ≠ 0 := by
  obtain ⟨x,hx⟩ := (double_comparison F e r h hr).1
  intro hz
  rw [hz] at hx
  simp [PortPair.pairSum] at hx

/-- Compare one surviving factor to a disjoint known X contraction. -/
theorem factor_eq_of_disjoint_X (F : Tensor ℂ ι) (e r : PortPair ι)
    (h : e.Disjoint r) (hr : XAt F r)
    (P : Matching (Remaining e.first e.second))
    (p q : Fin P.count → ℂ) (c : ℂ)
    (hp : ∀ j, p j ≠ 0) (hq : ∀ j, q j ≠ 0)
    (he : contraction F e = product P p q c)
    (j : Fin P.count) (hav : Avoids P j (e.residual r h)) : p j = q j := by
  obtain ⟨hnz,hflat⟩ := double_comparison F e r h hr
  rw [he] at hnz hflat
  exact surviving_factor_eq P p q c hp hq j _ hav hnz hflat

/-- The actual original-port edge corresponding to a residual factor. -/
def originalEdge (e : PortPair ι) (P : Matching (Remaining e.first e.second))
    (j : Fin P.count) : PortPair ι where
  first := (P.ports (j,false)).val
  second := (P.ports (j,true)).val
  distinct := by
    intro he
    have hh := P.ports.injective (Subtype.ext he)
    simp at hh

theorem avoids_of_disjoint_original (e r : PortPair ι) (h : e.Disjoint r)
    (P : Matching (Remaining e.first e.second)) (j : Fin P.count)
    (hd : (originalEdge e P j).Disjoint r) : Avoids P j (e.residual r h) := by
  obtain ⟨ha,hb,hc,hd⟩ := hd
  exact ⟨fun he => ha (congrArg Subtype.val he),
    fun he => hb (congrArg Subtype.val he),
    fun he => hc (congrArg Subtype.val he),
    fun he => hd (congrArg Subtype.val he)⟩

/-- A pair avoiding any three prescribed pairs exists on eight ports. -/
theorem exists_disjoint_three [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (e f g : PortPair ι) : ∃ r : PortPair ι,
      e.Disjoint r ∧ f.Disjoint r ∧ g.Disjoint r := by
  classical
  let s : Finset ι := {e.first,e.second,f.first,f.second,g.first,g.second}
  have hs : s.card ≤ 6 := by
    dsimp [s]
    have h₁ := Finset.card_insert_le e.first ({e.second,f.first,f.second,g.first,g.second} : Finset ι)
    have h₂ := Finset.card_insert_le e.second ({f.first,f.second,g.first,g.second} : Finset ι)
    have h₃ := Finset.card_insert_le f.first ({f.second,g.first,g.second} : Finset ι)
    have h₄ := Finset.card_insert_le f.second ({g.first,g.second} : Finset ι)
    have h₅ : ({g.first,g.second} : Finset ι).card ≤ 2 := Finset.card_le_two
    omega
  have hcard : 1 < (Finset.univ \ s).card := by
    have hh := Finset.card_sdiff_add_card_eq_card (show s ⊆ Finset.univ from Finset.subset_univ _)
    simp only [Finset.card_univ] at hh
    omega
  obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp hcard
  have ha' : a ≠ e.first ∧ a ≠ e.second ∧ a ≠ f.first ∧ a ≠ f.second ∧
      a ≠ g.first ∧ a ≠ g.second := by simpa [s] using (Finset.mem_sdiff.mp ha).2
  have hb' : b ≠ e.first ∧ b ≠ e.second ∧ b ≠ f.first ∧ b ≠ f.second ∧
      b ≠ g.first ∧ b ≠ g.second := by simpa [s] using (Finset.mem_sdiff.mp hb).2
  exact ⟨⟨a,b,hab⟩,
    ⟨ha'.1.symm,hb'.1.symm,ha'.2.1.symm,hb'.2.1.symm⟩,
    ⟨ha'.2.2.1.symm,hb'.2.2.1.symm,ha'.2.2.2.1.symm,hb'.2.2.2.1.symm⟩,
    ⟨ha'.2.2.2.2.1.symm,hb'.2.2.2.2.1.symm,ha'.2.2.2.2.2.symm,hb'.2.2.2.2.2.symm⟩⟩

/-- Source Lemma 8.4(1). This stronger algebraic form needs neither EO nor ARS:
all nonzero contractions may be arbitrary nonsingular anti-diagonal products.
The omitted zero contractions are proved nonzero by actual double sums. -/
theorem propagation_condition_one [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hd : WeightedDeck F) (base : PortPair ι)
    (hbase : ∀ r, base.Disjoint r → XAt F r) : ∀ e, XAt F e := by
  intro e
  obtain ⟨r,her,hbr⟩ := PortPair.exists_common_disjoint (by omega) e base
  obtain ⟨P,p,q,c,hc,hp,hq,he⟩ := hd e (nonzero_of_disjoint_X F e r her (hbase r hbr))
  rw [XAt,he]
  apply weighted_isX_of_equal P p q c hc hp
  intro j
  obtain ⟨r,hbr,her,hjr⟩ := exists_disjoint_three hn base e (originalEdge e P j)
  exact factor_eq_of_disjoint_X F e r her (hbase r hbr) P p q c hp hq he j
    (avoids_of_disjoint_original e r her P j hjr)

theorem propagation_condition_one_ARS [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hd : ARSDeck F) (base : PortPair ι)
    (hbase : ∀ r, base.Disjoint r → XAt F r) : ∀ e, XAt F e :=
  propagation_condition_one hn F hd.weighted base hbase

end Paper2.MatchingPropagation
