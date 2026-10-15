import Paper2.RelativeEO.WeightedComplementaryGraph
import Paper2.NetworkSubstitution

/-! Every weight-two complementary support is put into the canonical ordering
by an actual boundary permutation. The two-copy graph then substitutes the
permuted source corollas, retaining only original D-labelled resources. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput

noncomputable def complementaryTable (s : Fin 4 → Bool) (p q : AlgebraicComplex) :
    Signature AlgebraicComplex 4 := fun x =>
  (if x = s then p else 0) + (if x = (fun i => !(s i)) then q else 0)

def pattern0101 : Fin 4 → Bool := quadWord false true false true

theorem pattern0101_weight : weight pattern0101 = 2 := by decide

theorem quadWord_eq_iff (x : Fin 4 → Bool) (a b c d : Bool) :
    x = quadWord a b c d ↔ x 0 = a ∧ x 1 = b ∧ x 2 = c ∧ x 3 = d := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rintro ⟨h0, h1, h2, h3⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3

theorem complementaryTable_canonical (p q : AlgebraicComplex) :
    complementaryTable pattern0101 p q = weightedComplementary p q := by
  funext x
  have hb : (fun i => !(pattern0101 i)) = quadWord true false true false := by
    funext i
    fin_cases i <;> rfl
  unfold complementaryTable
  rw [hb]
  simp only [pattern0101, quadWord_eq_iff, weightedComplementary]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [h0, h1, h2, h3]

/-- Weight-two support supplies a concrete port equivalence; both complementary
words, both coefficients, and the order of every transformed port are retained. -/
theorem complementaryTable_reindex (s : Fin 4 → Bool) (hs : weight s = 2)
    (p q : AlgebraicComplex) :
    ∃ e : Equiv.Perm (Fin 4),
      Tensor.reindex e (complementaryTable s p q) = weightedComplementary p q := by
  obtain ⟨e, he⟩ := exists_portPermutation_of_weight_eq s pattern0101
    (hs.trans pattern0101_weight.symm)
  have hi : Function.Injective (fun x : Fin 4 → Bool => fun i => x (e i)) := by
    intro x y h
    funext j
    simpa using congrFun h (e.symm j)
  have hb : (fun i => !(pattern0101 (e i))) = fun i => !(s i) := by
    funext i
    exact congrArg Bool.not (congrFun he i)
  refine ⟨e, ?_⟩
  rw [← complementaryTable_canonical]
  funext x
  have hx : (fun i => x (e i)) = s ↔ x = pattern0101 := by rw [← he]; exact hi.eq_iff
  have hx' : (fun i => x (e i)) = (fun i => !(s i)) ↔ x = (fun i => !(pattern0101 i)) := by
    rw [← hb]
    constructor
    · intro hh
      apply hi
      exact hh
    · rintro rfl
      rfl
  simp only [Tensor.reindex, complementaryTable, hx, hx']

/-- Actual two-copy normalization over the original, unpermuted resource table.
The incidence maps carry the permutation, and substitution removes every formal
canonical-table label. No pins or coordinate slices are treated as resources. -/
theorem complementaryTable_network {F : SignatureFamily AlgebraicComplex}
    (s : Fin 4 → Bool) (hs : weight s = 2) (p q : AlgebraicComplex)
    (hD : (⟨4, complementaryTable s p q⟩ : AnySignature AlgebraicComplex) ∈ F) :
    ∃ N : Network AlgebraicComplex 4,
      N.Uses F ∧ N.NativeX ∧ N.denote = fun x => (p * q) * complementaryE x := by
  obtain ⟨e, he⟩ := complementaryTable_reindex s hs p q
  let R := (Network.corolla (complementaryTable s p q)).reindexBoundary e
  have hRU : R.Uses F := fun _ => hD
  have hRX : R.NativeX := fun i => Fin.elim0 i
  have hRd : R.denote = weightedComplementary p q := by
    rw [Network.denote_reindexBoundary, Network.denote_corolla]
    exact he
  let G := weightedNetwork p q
  let replacements : (v : Fin G.shape.vertices) → Network AlgebraicComplex (G.shape.arity v) := fun _ => R
  refine ⟨G.substitute replacements, G.substitute_uses replacements (fun _ => hRU),
    G.substitute_nativeX replacements (weightedNetwork_nativeX p q) (fun _ => hRX), ?_⟩
  rw [G.denote_substitute replacements (weightedNetwork_nativeX p q) (fun _ => hRX) (fun _ => hRd)]
  exact weightedNetwork_denote p q

end Paper2.RelativeEO
