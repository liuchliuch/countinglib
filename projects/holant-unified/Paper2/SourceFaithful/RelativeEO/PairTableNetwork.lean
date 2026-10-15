import Paper2.RelativeEO.PairTableNetwork
import Paper2.SourceFaithful.RelativeEO.WeightedComplementaryExit

/-! Canonical fixed-field answer version of the proved local construction.
The pure signatures/networks are unchanged. Machine reductions are proved again
from the separately named source-exact records; no output-code conversion or
old strict-root classification is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO

theorem realized_complementary_hard (G : Paper1DirectGadgetAccepted)
    (P : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (s : Fin 4 → Bool) (hs : weight s = 2)
    (p q : AlgebraicComplex) (hp : p ≠ 0) (hq : q ≠ 0)
    (hD : NativeNetworkRealizesUpTo L.family (complementaryTable s p q)) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  have hscomp : s ≠ (fun i => !(s i)) := by
    intro he
    have hh := congrFun he 0
    exact Bool.not_ne_self (s 0) hh.symm
  have hnon : complementaryTable s p q ≠ 0 := by
    intro hz
    have hh := congrFun hz s
    simp [complementaryTable,hscomp,hp] at hh
  obtain ⟨M,hM,hML⟩ := G.adjoin L _ hD
  have hLM : L.family ⊆ M.family := by rw [hM]; exact Set.subset_insert _ _
  have hpreM : Preprocessed M.family := by
    intro t ht
    rw [hM] at ht
    rcases ht with rfl | ht
    · exact ⟨by change 0 < (4 : ℕ); decide,hnon⟩
    · exact hpre t ht
  have hbothM : BothChargeSigns M.family := by
    obtain ⟨⟨f,hf,x,hx,hn⟩,⟨g,hg,y,hy,hp⟩⟩ := hboth
    exact ⟨⟨f,hLM hf,x,hx,hn⟩,⟨g,hLM hg,y,hy,hp⟩⟩
  have hnotM : ¬ Tract (kImage M) := fun ht =>
    hnot (ht.mono_family (familyAction_mono sourceKBasis hLM))
  exact (complementary_hard G P F U M hpreM hbothM hnotM s hs p q hp hq
    (by rw [hM]; exact Set.mem_insert _ _)).transport hML


end Paper2.SourceFaithful.RelativeEO
