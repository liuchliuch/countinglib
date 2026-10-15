import Paper2.SourceFaithful.SourceStatements.ThreeMatchingLineStatement
import Paper2.HeightOne.Dihedral.HighArityDeck
import Paper2.HeightOne.TensorPrimeTools

/-! Source Proposition 5.16 and Lemma 5.17. The hypotheses use the literal
signed first-contraction deck on arbitrary ordered ports. This is weaker than
the source's closure under one or more successive contractions. No common
matching, tensor factor or Segre ruling is supplied by the caller. -/
namespace Paper2.SourceFaithful.SourceStatements.DihedralRuling
noncomputable section
open Holant Holant.Marked Holant.Certificates
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.SectorRuling
open Holant.Dihedral.TwoCardLocalization (DifferentProducts presentationMatching)
open Holant.Dihedral.EndpointParallelogram (Pairing)
open Paper2.HeightOne.Dihedral.HighArity
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- A literal product on all disjoint matched pairs except one, multiplied by
one binary table on that fixed remaining pair. The latter may be zero. -/
def rulingValue {n k : ℕ} (p : (Fin k × Bool) ≃ Fin n)
    (A : Fin k → Mat) (e : Fin k) (h : Mat) : Signature Scalar n :=
  fun x => (∏ j ∈ ({e}ᶜ : Finset (Fin k)),
    A j (x (p (j,false))) (x (p (j,true)))) * h (x (p (e,false))) (x (p (e,true)))

/-- The whole affine pencil has one fixed literal product H and one fixed
varying port pair. All scalar phases, including zero/proportional members,
are retained in the conclusion. -/
def WholeRuling {n : ℕ} (Q : Scalar → Signature Scalar n) : Prop :=
  ∃ k : ℕ,∃ (p : (Fin k × Bool) ≃ Fin n) (A : Fin k → Mat)
    (e : Fin k) (h : Scalar → Mat),
    (∀ j,IsMonomial (A j)) ∧ ∀ t,Q t = rulingValue p A e (h t)

private theorem product_ruling {r : ℕ}
    (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2)) (A : Fin (r+1) → Mat)
    (κ : Scalar) (e : Fin (r+1)) :
    Holant.Dihedral.CompatibleClosure.productValue p A κ = rulingValue p A e (scale κ (A e)) := by
  funext x
  unfold Holant.Dihedral.CompatibleClosure.productValue rulingValue
  rw [Fintype.prod_eq_mul_prod_compl e]
  simp only [scale]
  ring

private theorem product_ruling_projective {r : ℕ}
    (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2)) (A B : Fin (r+1) → Mat)
    (κ : Scalar) (e : Fin (r+1))
    (hp : ∀ j,j ≠ e → ProjectivelyEqual (B j) (A j)) :
    ∃ h : Mat,Holant.Dihedral.CompatibleClosure.productValue p B κ = rulingValue p A e h := by
  classical
  have hc : ∀ j : Fin (r+1),∃ c : Scalar,c ≠ 0 ∧ (j ≠ e → B j = scale c (A j)) := by
    intro j
    by_cases hje : j = e
    · exact ⟨1,one_ne_zero,fun hn => False.elim (hn hje)⟩
    · obtain ⟨c,hc,heq⟩ := hp j hje
      exact ⟨c,hc,fun _ => heq⟩
  choose c hc heq using hc
  refine ⟨scale (κ * ∏ j ∈ ({e}ᶜ : Finset (Fin (r+1))),c j) (B e),?_⟩
  funext x
  unfold Holant.Dihedral.CompatibleClosure.productValue rulingValue
  rw [Fintype.prod_eq_mul_prod_compl e]
  have hout : (∏ j ∈ ({e}ᶜ : Finset (Fin (r+1))), B j (x (p (j,false))) (x (p (j,true)))) =
      (∏ j ∈ ({e}ᶜ : Finset (Fin (r+1))),c j) *
        ∏ j ∈ ({e}ᶜ : Finset (Fin (r+1))),A j (x (p (j,false))) (x (p (j,true))) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    rw [heq j (by simpa using hj)]
    rfl
  rw [hout]
  simp only [scale]
  ring

private theorem whole_ruling_from_span {r : ℕ} (U V : Signature Scalar (2*r+2))
    (a b : Scalar) (hab : a ≠ b)
    (p : (Fin (r+1) × Bool) ≃ Fin (2*r+2)) (A B : Fin (r+1) → Mat)
    (κ₀ κ₁ : Scalar) (hA : ∀ j,IsMonomial (A j))
    (hqa : tensorPencil U V a = Holant.Dihedral.CompatibleClosure.productValue p A κ₀)
    (hqb : tensorPencil U V b = Holant.Dihedral.CompatibleClosure.productValue p B κ₁)
    (e : Fin (r+1)) (hp : ∀ j,j ≠ e → ProjectivelyEqual (B j) (A j)) :
    WholeRuling (tensorPencil U V) := by
  obtain ⟨h₁,hh₁⟩ := product_ruling_projective p A B κ₁ e hp
  let h₀ := scale κ₀ (A e)
  refine ⟨r+1,p,A,e,(fun t u v => ((b-t)/(b-a))*h₀ u v + ((t-a)/(b-a))*h₁ u v),hA,?_⟩
  intro t
  rw [tensor_interpolation U V a b t hab,hqa,hqb,product_ruling p A κ₀ e,hh₁]
  funext x
  simp only [combination,rulingValue,h₀]
  ring

private theorem matching_presentation {r : ℕ} (g : Signature Scalar (2*r+2))
    (hg : MatchingOrZero monomialGroup g) (hn : g ≠ 0) :
    ∃ p : (Fin (r+1) × Bool) ≃ Fin (2*r+2),∃ A : Fin (r+1) → Mat,∃ κ : Scalar,
      (∀ j,IsMonomial (A j)) ∧ κ ≠ 0 ∧
        g = Holant.Dihedral.CompatibleClosure.productValue p A κ := by
  obtain ⟨M,hM,hκ,he⟩ := hg.resolve_left hn
  have hc := Fintype.card_congr M.ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hc
  have hcount : M.edges = r+1 := by omega
  cases M with
  | mk count p A κ =>
    dsimp only at hcount
    subst count
    exact ⟨p,A,κ,fun j => (safe_monomial_iff _).mp (hM j),hκ,he⟩

/-- The actual three-phase pencil relation and matching rigidity give the
complete one-pair ruling; no projective-factor witness is an input. -/
theorem pencil_whole_ruling {N r : ℕ} (hN : 3 ≤ N)
    (U V : Signature Scalar (2*r+2))
    (hs : ∀ t,Roots N t → MatchingOrZero monomialGroup (tensorPencil U V t))
    (hd : ∀ a b,Roots N a → Roots N b →
      ¬ DifferentProducts monomialGroup (2*r+2) (tensorPencil U V a) (tensorPencil U V b)) :
    WholeRuling (tensorPencil U V) := by
  classical
  by_cases hex : ∃ a,Roots N a ∧ tensorPencil U V a ≠ 0
  · obtain ⟨a,ha,hna⟩ := hex
    obtain ⟨b,hb,hab,hnb⟩ := two_nonzero_samples hN U V a ha hna
    obtain ⟨p₀,A₀,κ₀,hA₀,hκ₀,hqa⟩ := matching_presentation _ (hs a ha) hna
    obtain ⟨p₁,A₁,κ₁,hA₁,hκ₁,hqb⟩ := matching_presentation _ (hs b hb) hnb
    obtain ⟨c,hc,hca,hcb⟩ := third_root hN a b ha hb
    let α := (b-c)/(b-a)
    let β := (c-a)/(b-a)
    have hα : α ≠ 0 := div_ne_zero (sub_ne_zero.mpr hcb.symm) (sub_ne_zero.mpr hab.symm)
    have hβ : β ≠ 0 := div_ne_zero (sub_ne_zero.mpr hca) (sub_ne_zero.mpr hab.symm)
    by_cases hzc : tensorPencil U V c = 0
    · have hbprop : tensorPencil U V b = (-α/β) • tensorPencil U V a := by
        funext x
        have hx := congrFun (tensor_interpolation U V a b c hab) x
        rw [hzc] at hx
        change (0 : Scalar) = α * tensorPencil U V a x + β * tensorPencil U V b x at hx
        change tensorPencil U V b x = (-α/β) * tensorPencil U V a x
        calc
          tensorPencil U V b x = (-α * tensorPencil U V a x) / β :=
            (eq_div_iff hβ).mpr (by linear_combination -hx)
          _ = (-α/β) * tensorPencil U V a x := by ring
      have hqb' : tensorPencil U V b =
          Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ ((-α/β)*κ₀) := by
        rw [hbprop,hqa]
        funext x
        simp only [Pi.smul_apply,smul_eq_mul,Holant.Dihedral.CompatibleClosure.productValue]
        ring
      exact whole_ruling_from_span U V a b hab p₀ A₀ A₀ κ₀ ((-α/β)*κ₀)
        hA₀ hqa hqb' ⟨0,by omega⟩ (fun j _ => ProjectivelyEqual.refl _)
    · obtain ⟨p₂,A₂,κ₂,hA₂,hκ₂,hqc⟩ := matching_presentation _ (hs c hc) hzc
      have hrel : Holant.Dihedral.CompatibleClosure.productValue p₂ A₂ κ₂ =
          combination α β (Holant.Dihedral.CompatibleClosure.productValue p₀ A₀ κ₀)
            (Holant.Dihedral.CompatibleClosure.productValue p₁ A₁ κ₁) := by
        rw [←hqc,tensor_interpolation U V a b c hab,hqa,hqb]
      rcases Paper2.SourceFaithful.SourceStatements.source_5_15 p₀ p₁ p₂ A₀ A₁ A₂
        κ₀ κ₁ κ₂ α β hA₀ hA₁ hA₂ hκ₀ hκ₁ hκ₂ hα hβ hrel with h | h
      · obtain ⟨_,L₁,L₂,e,he⟩ := h
        have hqb' : tensorPencil U V b =
            Holant.Dihedral.CompatibleClosure.productValue p₀ (L₁.factors A₁) κ₁ :=
          hqb.trans (L₁.product_eq A₁ κ₁).symm
        exact whole_ruling_from_span U V a b hab p₀ A₀ (L₁.factors A₁)
          κ₀ κ₁ hA₀ hqa hqb' e (fun j hj => (he j hj).1)
      · obtain ⟨C,_⟩ := h
        exfalso
        apply hd a b ha hb
        let M₀ : Presentation Scalar (Fin (2*r+2)) := ⟨r+1,p₀,A₀,κ₀⟩
        let M₁ : Presentation Scalar (Fin (2*r+2)) := ⟨r+1,p₁,A₁,κ₁⟩
        refine ⟨M₀,M₁,fun j => (safe_monomial_iff _).mpr (hA₀ j),
          fun j => (safe_monomial_iff _).mpr (hA₁ j),hκ₀,hκ₁,hqa,hqb,?_⟩
        intro hm
        have hx := congrArg (fun z => z C.a) hm
        change (Pairing.ofPorts p₀).mate C.a = (Pairing.ofPorts p₁).mate C.a at hx
        rw [C.first_ab,C.second_ac] at hx
        exact C.bc hx
  · obtain ⟨b,hb,hb1,_⟩ := third_root hN 1 1 (Roots.one N) (Roots.one N)
    have hz (t : Scalar) (ht : Roots N t) : tensorPencil U V t = 0 := by
      by_contra hn
      exact hex ⟨t,ht,hn⟩
    obtain ⟨hU,hV⟩ := tensor_two_zeros U V 1 b (Ne.symm hb1)
      (hz 1 (Roots.one N)) (hz b hb)
    refine ⟨r+1,pairPorts r,(fun _ => Holant.Signature.equality),⟨0,by omega⟩,
      (fun _ => 0),(fun _ => equality_isMonomial),?_⟩
    intro t
    funext x
    simp [tensorPencil,hU,hV,rulingValue]

private theorem shifted_pencil_whole_ruling {N r : ℕ} (hN : 3 ≤ N)
    (U V : Signature Scalar (2*r+4))
    (hs : ∀ t,Roots N t → MatchingOrZero monomialGroup (tensorPencil U V t))
    (hd : ∀ a b,Roots N a → Roots N b →
      ¬ DifferentProducts monomialGroup (2*r+4) (tensorPencil U V a) (tensorPencil U V b)) :
    WholeRuling (tensorPencil U V) := by
  have hn : 2*r+4 = 2*(r+1)+2 := by omega
  generalize hc : 2*r+4 = n at U V hs hd ⊢
  have he : n = 2*(r+1)+2 := hc.symm.trans hn
  clear hc hn
  subst n
  exact pencil_whole_ruling hN U V hs hd

/-- Source Proposition 5.16, on every original ordered pair and xor sector.
The fixed product and the remaining pair are derived from the signed deck.
The conclusion is an equality of literal tables for every scalar parameter,
so zero members and proportional pencils are included. -/
theorem source_5_16 {N : ℕ} (hN : 3 ≤ N) (r : ℕ) (hr : 1 ≤ r)
    (f : Paper2.Signature Scalar (2*r+6))
    (hcards : ∀ i : PhaseLabel N,∀ p : Equiv.Perm (Fin (2*r+6)),
      MatchingOrZero monomialGroup
        (Holant.Signature.contract (phaseKernel i)
          (Holant.Tensor.reindex p.symm (Paper2.HeightOne.PhaseCards.walshCoordinates f))))
    (order : Equiv.Perm (Fin (2*r+6))) (γ : Bool) :
    WholeRuling (fun s => Holant.Signature.contract (M γ (-s))
      (Holant.Tensor.reindex order.symm (Paper2.HeightOne.PhaseCards.walshCoordinates f))) := by
  let q := Holant.Tensor.reindex order.symm (Paper2.HeightOne.PhaseCards.walshCoordinates f)
  have hqcards (i : PhaseLabel N) (p : Equiv.Perm (Fin (2*r+6))) :
      MatchingOrZero monomialGroup
        (Holant.Signature.contract (phaseKernel i) (Holant.Tensor.reindex p.symm q)) := by
    exact hcards i (p.trans order)
  let U : Signature Scalar (2*r+4) := fun x => q (Fin.cons false (Fin.cons γ x))
  let V : Signature Scalar (2*r+4) := fun x => -q (Fin.cons true (Fin.cons (!γ) x))
  have hpencil (s : Scalar) : Holant.Signature.contract (M γ (-s)) q = tensorPencil U V s := by
    funext x
    cases γ <;> simp [Holant.Signature.contract,M,monomial,tensorPencil,U,V] <;> ring
  have hs (s : Scalar) (hs : Roots N s) :
      MatchingOrZero monomialGroup (tensorPencil U V s) := by
    rw [← hpencil s]
    simpa only [phaseKernel,Equiv.refl_symm,Holant.Tensor.reindex_refl] using
      hqcards (γ,⟨s,hs⟩) (Equiv.refl _)
  have hd (a b : Scalar) (ha : Roots N a) (hb : Roots N b) :
      ¬ DifferentProducts monomialGroup (2*r+4) (tensorPencil U V a) (tensorPencil U V b) := by
    rw [← hpencil a,← hpencil b]
    exact no_different_matching_cards r hr q (M false (-1))
      (M_isMonomial false (by norm_num))
      (fun p => hqcards (false,⟨1,Roots.one N⟩) p)
      (M γ (-a)) (M γ (-b))
      (M_isMonomial γ (neg_ne_zero.mpr (ha.ne_zero (by omega))))
      (M_isMonomial γ (neg_ne_zero.mpr (hb.ne_zero (by omega))))
  have he : (fun s => Holant.Signature.contract (M γ (-s)) q) = tensorPencil U V :=
    funext hpencil
  change WholeRuling (fun s => Holant.Signature.contract (M γ (-s)) q)
  rw [he]
  exact shifted_pencil_whole_ruling hN U V hs hd

/-- The arbitrary original signed first deck already suffices for the
proper tensor decomposition in source Lemma 5.17, after the actual invertible
Walsh transport. No minimal-prime, safety or retained-stage premise is added. -/
theorem source_5_17 {N : ℕ} (hN : 3 ≤ N) (r : ℕ) (hr : 1 ≤ r)
    (f : Paper2.Signature Scalar (2*r+6)) (hf : f ≠ 0)
    (hcards : ∀ i : PhaseLabel N,∀ p : Equiv.Perm (Fin (2*r+6)),
      MatchingOrZero monomialGroup
        (Holant.Signature.contract (phaseKernel i)
          (Holant.Tensor.reindex p.symm (Paper2.HeightOne.PhaseCards.walshCoordinates f)))) :
    ∃ m k : ℕ,∃ hm : 0 < m,∃ hk : 0 < k,∃ e : Fin (m+k) ≃ Fin (2*r+6),
      ∃ a : Paper2.Signature Scalar m,∃ b : Paper2.Signature Scalar k,
        Paper2.Tensor.reindex e (Paper2.Signature.tensor a b) = f := by
  have hn : ¬ Paper2.TensorPrime f := by
    intro hp
    have hw := Paper2.HeightOne.tensorPrime_action
      Paper2.HeightOne.PhaseCards.walshBasis.symm hp
    rw [Paper2.HeightOne.PhaseCards.walshBasis_inverse_action] at hw
    exact signed_deck_not_tensorPrime hN r hr _ hcards hw
  have hfactor : ¬ (∀ m k : ℕ,0 < m → 0 < k → ∀ e : Fin (m+k) ≃ Fin (2*r+6),
      ∀ a : Paper2.Signature Scalar m,∀ b : Paper2.Signature Scalar k,
        Paper2.Tensor.reindex e (Paper2.Signature.tensor a b) ≠ f) :=
    fun h => hn ⟨hf,h⟩
  push Not at hfactor
  obtain ⟨m,k,hm,hk,e,a,b,he⟩ := hfactor
  exact ⟨m,k,hm,hk,e,a,b,he⟩


end
end Paper2.SourceFaithful.SourceStatements.DihedralRuling
