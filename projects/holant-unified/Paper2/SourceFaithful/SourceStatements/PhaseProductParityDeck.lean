import Paper2.SourceFaithful.SourceStatements.PhaseProductParityRows
import Paper2.HeightOne.Dihedral.ActualQuaternary

/-! A local, literal ordered contraction condition for one quaternary
Walsh tensor. It retains zero cards; the nonzero cards have one parity and
the exact nonsingular rotation/reflection coefficient ratio. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards EndpointSelfLoop

def BinaryPhase (N : ℕ) {ι : Type} [Fintype ι]
    (g : Tensor AlgebraicComplex ι) : Prop :=
  HasParity g ∧ ∀ x, RootComplement N (g x) (g (fun j => !(x j)))

def DihedralContractions (N : ℕ) (f : Signature AlgebraicComplex 4) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (u v : Bool) (s : AlgebraicComplex), Root N s →
    BinaryPhase N (card (xorKernel u v s) i j hij f)

lemma safe_pair_iff (N : ℕ) (a b : AlgebraicComplex) :
    ((a = 0 ∧ b = 0) ∨ ∃ η κ, Root N η ∧ κ ≠ 0 ∧ a = κ ∧ b = -κ * η) ↔
      RootComplement N a b := by
  constructor
  · rintro (h | ⟨η,κ,hη,hκ,rfl,hb⟩)
    · exact Or.inl h
    · exact Or.inr ⟨η,hη,hκ,by rw [hb]; ring⟩
  · intro h
    exact h.safe

lemma parity_extend_bits (i j : Fin 4) (hij : i ≠ j)
    (y : Remaining i j → Bool) (u v : Bool) :
    parity (extendBits i j hij y u v) =
      (parity y + (if u then 1 else 0) + (if v then 1 else 0)) % 2 := by
  classical
  have hw := weight_reindex (splitPorts i j hij)
    (Sum.elim y (fun b : Bool => if b then v else u))
  change weight (extendBits i j hij y u v) = _ at hw
  rw [weight_sum] at hw
  simp only [weight, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte] at hw
  change weight (extendBits i j hij y u v) =
    weight y + ((if v then 1 else 0) + (if u then 1 else 0)) at hw
  unfold parity
  rw [hw]
  cases u <;> cases v <;> simp [Nat.add_mod]
  omega

lemma xor_card_hasParity {f : Signature AlgebraicComplex 4} (hp : HasParity f)
    (i j : Fin 4) (hij : i ≠ j) (u v : Bool) (s : AlgebraicComplex) :
    HasParity (card (xorKernel u v s) i j hij f) := by
  intro x y hx hy
  rw [card_xor_apply] at hx hy
  have ex : f (extendBits i j hij x u v) ≠ 0 ∨
      f (extendBits i j hij x (!u) (!v)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (by simp [h])
  have ey : f (extendBits i j hij y u v) ≠ 0 ∨
      f (extendBits i j hij y (!u) (!v)) ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (by simp [h])
  rcases ex with ex | ex <;> rcases ey with ey | ey
  all_goals have h := hp _ _ ex ey
  all_goals rw [parity_extend_bits,parity_extend_bits] at h
  all_goals have hpx := Nat.mod_lt (weight x) (by omega : 0 < 2)
  all_goals have hpy := Nat.mod_lt (weight y) (by omega : 0 < 2)
  all_goals cases u <;> cases v <;> simp only [Bool.not_false,Bool.not_true,
    Bool.false_eq_true,↓reduceIte] at h <;> unfold parity at * <;> omega

theorem local_dihedral_iff {N : ℕ} (hN : 3 ≤ N)
    (f : Signature AlgebraicComplex 4) :
    DihedralContractions N f ↔ HasParity f ∧ FullQuaternaryDeck N f := by
  constructor
  · intro h
    obtain ⟨ζ,hζ⟩ := exists_algebraic_primitiveRoot N (by omega)
    refine ⟨hasParity_of_root_of_unity_contractions (by simp) N hN ζ hζ f ?_,?_⟩
    · intro i j hij s hs
      simpa only [xorKernel_false_false,card_plus] using
        (h i j hij false false s hs).1
    · intro i j hij a
      apply (provedPhasePencil.phasePencil_7_1 N hN _ _ _ _).mpr
      intro s hs
      have hc := (h i j hij (a i) (a j) s hs).2 (restrict i j a)
      rw [card_xor_apply,card_xor_apply,extendBits_restrict,
        extendBits_flipPair,extendBits_flipRemaining,extendBits_flipAll] at hc
      exact hc.safe
  · rintro ⟨hp,hd⟩ i j hij u v s hs
    refine ⟨xor_card_hasParity hp i j hij u v s,?_⟩
    intro x
    let a := extendBits i j hij x u v
    have hui : a i = u := by simp [a,extendBits,splitPorts]
    have hvj : a j = v := by simp [a,extendBits,splitPorts,Ne.symm hij]
    have hr : restrict i j a = x := by
      funext k
      dsimp only [a,restrict,extendBits,splitPorts]
      simp [k.property.1,k.property.2]
      rfl
    have hc := (provedPhasePencil.phasePencil_7_1 N hN _ _ _ _).mp (hd i j hij a) s hs
    apply (safe_pair_iff _ _ _).mp
    rw [← extendBits_flipRemaining i j hij a,
      ← extendBits_flipPair i j hij a,← extendBits_flipAll i j hij a,
      hui,hvj,hr] at hc
    simpa only [card_xor_apply, a] using hc

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity
