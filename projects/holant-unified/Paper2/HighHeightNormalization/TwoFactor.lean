import Paper2.HighHeightNormalization.PortFactor

/-! Exact two-factor coefficient comparison for the distinct-mates branch. -/
namespace Paper2.HighHeightNormalization
open MatchingPropagation CommonPhase EndpointSelfLoop
variable {ι : Type}

theorem product_two (P : Matching ι) (p q : Fin P.count → ℂ) (c : ℂ)
    (j k : Fin P.count) (hjk : j ≠ k) (b d : Bool)
    (hother : ∀ i, i ≠ j → i ≠ k → p i = q i) (x : ι → Bool) :
    product P p q c x =
      (if x (P.ports (j,b)) = b then p j else q j) *
      (if x (P.ports (k,d)) = d then p k else q k) *
      (c * ∏ i ∈ (Finset.univ.erase j).erase k, p i) * literal P ℂ x := by
  classical
  rw [product_coeff_literal]
  by_cases hx : Transversal P x
  · have hl : literal P ℂ x = 1 := by simp [literal,hx]
    rw [hl,mul_one,mul_one]
    have hkj : k ∈ Finset.univ.erase j := by simp [hjk.symm]
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ _ hkj]
    have hp : (∏ i ∈ (Finset.univ.erase j).erase k,
        if x (P.ports (i,false)) then q i else p i) =
        ∏ i ∈ (Finset.univ.erase j).erase k, p i := by
      apply Finset.prod_congr rfl
      intro i hi
      have hik := (Finset.mem_erase.mp hi).1
      have hij := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      rw [← hother i hij hik]
      split <;> rfl
    rw [hp]
    have orient (i : Fin P.count) (t : Bool) :
        (if x (P.ports (i,false)) then q i else p i) =
          if x (P.ports (i,t)) = t then p i else q i := by
      have ht := hx i
      cases t <;> cases h₀ : x (P.ports (i,false)) <;>
        cases h₁ : x (P.ports (i,true)) <;> simp [h₀,h₁] at ht ⊢
    rw [orient j b,orient k d]
    ring
  · simp [literal,hx]

/-- Every port orientation is retained explicitly in the two exceptional
binary factors; all other factors have their exact constant coefficients. -/
theorem product_two_phase (P : Matching ι) (z : Fin P.count → ℂ) (c : ℂ)
    (hc : c ≠ 0) (hz : ∀ i, z i ≠ 0)
    (a b : ι) (hi : (P.ports.symm a).1 ≠ (P.ports.symm b).1)
    (hother : ∀ i, i ≠ (P.ports.symm a).1 → i ≠ (P.ports.symm b).1 → z i = star (z i)) :
    ∃ w v C : ℂ, w ≠ 0 ∧ v ≠ 0 ∧ C ≠ 0 ∧
      product P z (fun i => star (z i)) c =
        fun x => phaseWeight w (x a) * phaseWeight v (x b) * C * literal P ℂ x := by
  classical
  let j := (P.ports.symm a).1
  let k := (P.ports.symm b).1
  let s := (P.ports.symm a).2
  let t := (P.ports.symm b).2
  let w := if s then star (z j) else z j
  let v := if t then star (z k) else z k
  let C := c * ∏ i ∈ (Finset.univ.erase j).erase k, z i
  refine ⟨w,v,C,?_,?_,?_,?_⟩
  · dsimp [w]; cases s <;> simpa using hz j
  · dsimp [v]; cases t <;> simpa using hz k
  · exact mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun i _ => hz i))
  · funext x
    rw [product_two P z (fun i => star (z i)) c j k hi s t hother]
    have ha : P.ports (j,s) = a := P.ports.apply_symm_apply a
    have hb : P.ports (k,t) = b := P.ports.apply_symm_apply b
    rw [ha,hb]
    have h₁ : (if x a = s then z j else star (z j)) = phaseWeight w (x a) := by
      dsimp [w,phaseWeight]; cases s <;> cases x a <;> simp
    have h₂ : (if x b = t then z k else star (z k)) = phaseWeight v (x b) := by
      dsimp [v,phaseWeight]; cases t <;> cases x b <;> simp
    rw [h₁,h₂]

/-- For an unmatched deleted pair, exactly one actual summand survives on
each transversal assignment with opposite deleted bits. -/
theorem pairSum_eq_on_transversal (P : Matching ι) (e : PortPair ι)
    (hm : mate P e.first ≠ e.second) (F : Tensor ℂ ι)
    (hsupport : ∀ x, ¬Transversal P x → F x = 0)
    (x : ι → Bool) (hx : Transversal P x) (he : x e.second = !(x e.first)) :
    e.pairSum F x = F x := by
  classical
  rw [PortPair.pairSum_eq_loop,loop_apply_restrict _ _ _ _ x he]
  have hnot : ¬Transversal P (fun i => x (Equiv.swap e.first e.second i)) := by
    intro ht
    have h₁ := (transversal_iff_mate P _).mp ht e.first
    have h₂ := (transversal_iff_mate P _).mp hx e.first
    rw [Equiv.swap_apply_left,Equiv.swap_apply_of_ne_of_ne (mate_ne P _) hm,he,
      Bool.not_not] at h₁
    rw [h₁] at h₂
    cases x e.first <;> simp at h₂
  rw [hsupport _ hnot,add_zero]

set_option maxHeartbeats 400000 in
/-- Flatness of the actual splice forces the two ordered ARS factors to
have the same projective ratio. Nonzero is derived from a transversal word. -/
theorem two_phase_ratio (P : Matching ι) (e : PortPair ι)
    (hm : mate P e.first ≠ e.second) (z w c : ℂ)
    (hz : z ≠ 0) (hw : w ≠ 0) (hc : c ≠ 0)
    (hflat : Flat (e.pairSum (fun x =>
      phaseWeight z (x e.first) * phaseWeight w (x e.second) * c * literal P ℂ x))) :
    star z * w = z * star w := by
  let F : Tensor ℂ ι := fun x =>
    phaseWeight z (x e.first) * phaseWeight w (x e.second) * c * literal P ℂ x
  have hs : ∀ x, ¬Transversal P x → F x = 0 := by
    intro x hx; simp [F,literal,hx]
  obtain ⟨x,hx,he⟩ := exists_literal_opposite (K := ℂ) P e.first e.second e.distinct
  have htx : Transversal P x := by by_contra h; simp [literal,h] at hx
  have hty : Transversal P (fun i => !(x i)) := (transversal_complement P x).mpr htx
  have hey : (!x e.second) = !(!x e.first) := by rw [he]
  have hcx := pairSum_eq_on_transversal P e hm F hs x htx he
  have hcy := pairSum_eq_on_transversal P e hm F hs (fun i => !(x i)) hty hey
  have hn (y : ι → Bool) (hy : Transversal P y) : F y ≠ 0 := by
    simpa [F,literal,hy] using
      mul_ne_zero (mul_ne_zero (phaseWeight_ne_zero hz (y e.first)) (phaseWeight_ne_zero hw (y e.second))) hc
  have hflat' : Flat (e.pairSum F) := hflat
  have hnx : e.pairSum F x ≠ 0 := hcx.symm ▸ hn x htx
  have hny : e.pairSum F (fun i => !(x i)) ≠ 0 := hcy.symm ▸ hn (fun i => !(x i)) hty
  have hh : F x = F (fun i => !(x i)) :=
    hcx.symm.trans ((hflat' x (fun i => !(x i)) hnx hny).trans hcy)
  change _ * c * literal P ℂ x = _ * c * literal P ℂ (fun i => !(x i)) at hh
  simp only [literal,if_pos htx,if_pos hty,mul_one] at hh
  have hratio := mul_right_cancel₀ hc hh
  rw [he] at hratio
  cases ha : x e.first <;> simp [phaseWeight,ha] at hratio
  · exact hratio.symm
  · exact hratio

/-- The exact table, with both scalar norm factors retained. -/
theorem two_phase_mating_eq (P : Matching ι) (a b : ι) (z w c : ℂ) :
    attach a (binary z) (attach b (binary w) (fun x =>
      phaseWeight z (x a) * phaseWeight w (x b) * c * literal P ℂ x)) =
      fun x => ((z * star z) * (w * star w) * c) * literal P ℂ x := by
  funext x
  simp only [attach_binary]
  have h (z : ℂ) (v : Bool) : matingWeight z v * phaseWeight z v = z * star z := by
    cases v <;> simp [matingWeight,phaseWeight,mul_comm]
  calc
    _ = (matingWeight z (x a) * phaseWeight z (x a)) *
        (matingWeight w (x b) * phaseWeight w (x b)) * c * literal P ℂ x := by ring
    _ = _ := by rw [h,h]

/-- Both exceptional factors are normalized by their two actual one-port
attachments, with all nonzero scalar factors retained. -/
theorem two_phase_mating (P : Matching ι) (a b : ι) (z w c : ℂ)
    (hz : z ≠ 0) (hw : w ≠ 0) (hc : c ≠ 0) :
    IsX (attach a (binary z) (attach b (binary w) (fun x =>
      phaseWeight z (x a) * phaseWeight w (x b) * c * literal P ℂ x))) := by
  refine ⟨P,(z * star z) * (w * star w) * c,?_,two_phase_mating_eq P a b z w c⟩
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hz (by simpa using hz))
    (mul_ne_zero hw (by simpa using hw))) hc

end Paper2.HighHeightNormalization
