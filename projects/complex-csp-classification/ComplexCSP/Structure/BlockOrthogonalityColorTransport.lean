import ComplexCSP.Algebra.LegalPurificationTables
import ComplexCSP.Recognition.GlobalConditions

/-! # Literal block orthogonality and legal purification under color equivalence -/
noncomputable section
open Classical
namespace ComplexCSP.BlockOrthogonalityColorTransport
open BlockOrthogonality RowTypes GeneratingSet
open scoped BigOperators
variable {D E X Y : Type} [Fintype D] [Fintype E]

/-- Reindexing equal-magnitude Hermitian sums uses the actual finite sum. -/
theorem vector_reindex (e : E ≃ D) {u v : D → ℂ} (h : VectorBlockOrthogonal u v) :
    VectorBlockOrthogonal (u ∘ e) (v ∘ e) := by
  intro z hz
  have hh := h (e z) hz
  have he := e.sum_comp (fun w => if ‖u w‖=‖u (e z)‖ then u w*star (v w) else 0)
  simp only [hermitianSum,magnitudeBlock,Finset.sum_filter] at hh ⊢
  exact he.trans hh

/-- Row restriction and a column bijection preserve the exact BO predicate. -/
theorem matrix_reindex (G : X → D → ℂ) (r : Y → X) (e : E ≃ D)
    (h : BlockOrthogonal G) : BlockOrthogonal (fun y z => G (r y) (e z)) := by
  have hn (x : Y) (hx : (fun z => G (r x) (e z))≠0) : G (r x)≠0 := by
    intro he
    apply hx
    funext z
    exact congrFun he (e z)
  constructor
  · intro x y hx hy
    rcases h.1 (r x) (r y) (hn x hx) (hn y hy) with hm | hd
    · obtain ⟨c,hc,hm⟩ := hm
      exact Or.inl ⟨c,hc,fun z => hm (e z)⟩
    · exact Or.inr (Set.disjoint_left.mpr (fun z hx hy => Set.disjoint_left.mp hd hx hy))
  · intro x y hx hy hm
    have hm' : MagnitudeProportional (G (r x)) (G (r y)) := by
      obtain ⟨c,hc,hm⟩ := hm
      exact ⟨c,hc,fun z => by simpa using hm (e.symm z)⟩
    rcases h.2 (r x) (r y) (hn x hx) (hn y hy) hm' with hp | ho
    · obtain ⟨c,hc,hp⟩ := hp
      exact Or.inl ⟨c,hc,fun z => hp (e z)⟩
    · exact Or.inr (vector_reindex e ho)

def tableReindex (T : PositiveTable D) (e : E ≃ D) : PositiveTable E :=
  ⟨T.rowArity,fun a => T.value (e ∘ a)⟩

omit [Fintype D] [Fintype E] in
theorem tableReindex_rows (T : PositiveTable D) (e : E ≃ D) (x : Fin T.rowArity → E) (z : E) :
    (tableReindex T e).rows x z=T.rows (e ∘ x) (e z) := by
  change T.value (e ∘ Fin.snoc x z)=T.value (Fin.snoc (e ∘ x) (e z))
  apply congrArg T.value
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp

omit [Fintype D] [Fintype E] in
theorem tableReindex_inverse (T : PositiveTable D) (e : E ≃ D) :
    tableReindex (tableReindex T e) e.symm=T := by
  cases T with
  | mk n v =>
    unfold tableReindex
    congr 1
    funext a
    simp [Function.comp_def]

omit [Fintype D] [Fintype E] in
private theorem purify_value_eq {S : Finset ℂˣ} (P : LegalGeneratingSet S)
    (G : X → D → ℂ) (H : Y → E → ℂ)
    (hG : LegalGeneratingSet.ContainsTable S G) (hH : LegalGeneratingSet.ContainsTable S H)
    (x : X) (z : D) (y : Y) (w : E) (he : G x z=H y w) :
    P.purifyTable G hG x z=P.purifyTable H hH y w := by
  by_cases hz : G x z=0
  · rw [P.purifyTable_zero G hG x z hz,P.purifyTable_zero H hH y w (he.symm.trans hz)]
  · have hw : H y w≠0 := by rwa [←he]
    rw [P.purifyTable_nonzero G hG x z hz,P.purifyTable_nonzero H hH y w hw]
    apply congrArg (fun g : LegalGeneratingSet.EntryGroup S => (P.purifiedHom g : ℂ))
    exact Subtype.ext (Units.ext he)

/-- The legal singleton choices are compared in one actual finite ambient set;
no equality of unrelated chosen generating bases is assumed. -/
theorem singleton_reindex (T : PositiveTable D) (e : E ≃ D)
    (h : BlockOrthogonal T.singletonRows) : BlockOrthogonal (tableReindex T e).singletonRows := by
  let U := tableReindex T e
  let S := T.nonzeroValues ∪ U.nonzeroValues
  let P := LegalGeneratingSet.choose S
  have hT : T.nonzeroValues⊆S := Finset.subset_union_left
  have hU : U.nonzeroValues⊆S := Finset.subset_union_right
  have hcontainsT : LegalGeneratingSet.ContainsTable S T.rows := by
    intro x z hz
    exact hT ((T.mem_nonzeroValues _).mpr ⟨x,z,rfl⟩)
  have hcontainsU : LegalGeneratingSet.ContainsTable S U.rows := by
    intro x z hz
    exact hU ((U.mem_nonzeroValues _).mpr ⟨x,z,rfl⟩)
  have hPT : BlockOrthogonal (P.purifyTable T.rows hcontainsT) :=
    (T.ambient_BO_iff P (LegalGeneratingSet.choose T.nonzeroValues) hT (Finset.Subset.refl _)).mpr h
  have hm := matrix_reindex (P.purifyTable T.rows hcontainsT) (fun x => e ∘ x) e hPT
  have he : (fun x z => P.purifyTable T.rows hcontainsT (e ∘ x) (e z))=
      P.purifyTable U.rows hcontainsU := by
    funext x z
    exact purify_value_eq P T.rows U.rows hcontainsT hcontainsU _ _ _ _ (tableReindex_rows T e x z).symm
  rw [he] at hm
  exact (U.ambient_BO_iff P (LegalGeneratingSet.choose U.nonzeroValues) hU (Finset.Subset.refl _)).mp hm

end ComplexCSP.BlockOrthogonalityColorTransport
