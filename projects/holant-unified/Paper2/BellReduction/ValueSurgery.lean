import Paper2.BellReduction.RawSurgerySemantics
import Paper2.Complexity.BellMachines.RawTripleValidated

/-! Source-labelled correctness of the actual finite-machine raw Bell surgery.
The statement is about the original validated Holant evaluator and its literal
algebraic family; formal tensor tables are not substituted for oracle inputs. -/
namespace Paper2.BellReduction
open Complexity ExactInput Tractable Problem Bell Bell.Closures ReedMuller
open RawOccurrence RawNative BellMachines.RawTriple

private theorem sigma_table_cast {r s : ℕ}
    {f : Signature AlgebraicComplex r} {g : Signature AlgebraicComplex s}
    (h : (⟨r,f⟩ : AnySignature AlgebraicComplex) = ⟨s,g⟩) (x : Fin s → Bool) :
    f (fun i => x (Fin.cast (congrArg Sigma.fst h) i)) = g x := by
  cases h
  rfl

/-- Reading a known literal family label agrees with its full ordered table. -/
theorem languageTable_literal (L : Language) (i : Fin L.count) {n : ℕ}
    (f : Signature AlgebraicComplex n)
    (hi : (⟨L.arity i.val,L.signature i⟩ : AnySignature AlgebraicComplex) = ⟨n,f⟩)
    (x : Fin n → Bool) : languageTable L i.val (List.ofFn x) = f x := by
  have ha := congrArg Sigma.fst hi
  have hx : (List.ofFn x).length = L.arity i.val := by simpa using ha.symm
  simp only [languageTable,dif_pos i.isLt,dif_pos hx]
  have he : (fun j => (List.ofFn x).get (Fin.cast hx.symm j)) =
      fun j => x (Fin.cast ha j) := by
    funext j
    simp
    rfl
  rw [he]
  exact sigma_table_cast hi x

/-- Each selected binary row has exactly two endpoints in the actual input. -/
theorem split_lengths (L : Language) (G : Instance L) (t : Split)
    (hs : splitThree G.val.vertices = some t) (hzero : L.arity 0 = 2) :
    t.first.length = 2 ∧ t.second.length = 2 ∧ t.third.length = 2 := by
  have hp := splitThree_perm hs
  have hlen (p : List RawEndpoint) (hm : (0,p) ∈ G.val.vertices) : p.length = 2 := by
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
    have hh := (G.property.1 i).2
    rw [hi] at hh
    exact hh.trans hzero
  exact ⟨hlen _ (hp.mem_iff.mpr (by simp)),hlen _ (hp.mem_iff.mpr (by simp)),
    hlen _ (hp.mem_iff.mpr (by simp))⟩

/-- One real invocation of `validComputes` has this exact algebraic effect.
The scalar has not yet been divided out, and no unit-cost arithmetic is claimed. -/
theorem value_transformValid (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
    (c : AlgebraicComplex) (d l : Bool) (hL0 : 0 < L.count)
    (hbell : (⟨L.arity 0,L.signature ⟨0,hL0⟩⟩ : AnySignature AlgebraicComplex) =
      ⟨2,bellTable d l⟩)
    (hcore : (⟨L.arity coreLabel,L.signature ⟨coreLabel,hl⟩⟩ : AnySignature AlgebraicComplex) =
      ⟨8,fun x => c * core x⟩)
    (G : TripleInstance L) :
    value .nativeX L (transformValid L hzero coreLabel hl ha G) =
      c * sign l * value .nativeX L G.val := by
  have hs := RawTripleBridge.splitThree_machine G.val.property hzero G.property
  have hlen := split_lengths L G.val _ hs hzero
  have hb : ∀ p ∈ G.val.val.endpoints, p.1 < G.val.val.edges.length := by
    intro p hp
    exact (G.val.val.mem_expectedEndpoints_iff p).mp (G.val.property.2.2.mem_iff.mp hp)
  have hB (a b : Bool) : languageTable L 0 [a,b] = ordered d l a b := by
    exact languageTable_literal L ⟨0,hL0⟩ _ hbell ![a,b]
  have hC (x : Fin 8 → Bool) : languageTable L coreLabel (List.ofFn x) = c * core x :=
    languageTable_literal L ⟨coreLabel,hl⟩ _ hcore x
  rw [← evaluate_language,← evaluate_language]
  exact evaluate_perform (languageTable L) G.val.val coreLabel _ hs hb
    hlen.1 hlen.2.1 hlen.2.2 c d l hB hC

end Paper2.BellReduction
