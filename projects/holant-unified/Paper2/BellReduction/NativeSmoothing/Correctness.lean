import Paper2.BellReduction.NativeSmoothing.NativeSmoothing
import Paper2.BellReduction.NativeSmoothing.Validation

/-! The native-edge eliminator is correct on every well-formed original raw
record, including a marked self-loop or two edges meeting the same vertex. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.BellReduction.NativeSmoothing.Surgery
open Complexity RawClosedNetwork Smoothing
variable {K : Type} [CommSemiring K]

 theorem endpoint_bound {r : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hr : r.WellFormed s b arity) {row : RawVertex} (hv : row ∈ r.vertices)
    {p : RawEndpoint} (hp : p ∈ row.2) : p.1 < r.edges.length := by
  have he : p ∈ r.endpoints := List.mem_flatten.mpr
    ⟨row.2,List.mem_map.mpr ⟨row,hv,rfl⟩,hp⟩
  exact (ends_mem _ _).mp ((hr.2.2.trans (by rw [expectedEndpoints_eq])).mem_iff.mp he)

/-- The local assignment sum uses exactly the original decoder's orientation. -/
theorem evaluate_eq_raw (T : Choice.Table K) (r : RawClosedNetwork)
    {s b : ℕ} {arity : ℕ → ℕ} (hr : r.WellFormed s b arity) :
    Choice.evaluate T r.edges.length r.vertices = RawNative.evaluate T r := by
  unfold Choice.evaluate Choice.weight RawNative.evaluate
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  apply List.map_congr_left
  intro row hv
  unfold Choice.rowValue RawNative.rowValue
  congr 1
  apply List.map_congr_left
  intro p hp
  simp only [Choice.bit,Choice.extend,RawNative.readEnd,dif_pos (endpoint_bound hr hv hp)]

 theorem record_partition (r : RawClosedNetwork) (v : Fin r.vertices.length)
    (p q : RawEndpoint) (hrow : (r.vertices.get v).2 = [p,q]) :
    (((r.vertices.get v).1,[p,q])::r.vertices.eraseIdx v.val).Perm r.vertices := by
  have hh : r.vertices[v.val] = ((r.vertices.get v).1,[p,q]) := Prod.ext rfl hrow
  simpa only [hh] using List.getElem_cons_eraseIdx_perm v.isLt

 theorem remainder_member (r : RawClosedNetwork) (v : ℕ)
    (row : RawVertex) (hr : row ∈ r.vertices.eraseIdx v)
    (p : RawEndpoint) (hp : p ∈ row.2) : p ∈ remainderEnds r v :=
  List.mem_flatten.mpr ⟨row.2,List.mem_map.mpr ⟨row,hr,rfl⟩,hp⟩

 theorem loop_mate (r : RawClosedNetwork) {s b : ℕ} {arity : ℕ → ℕ}
    (hr : r.WellFormed s b arity) (v : Fin r.vertices.length)
    (p q : RawEndpoint) (hrow : (r.vertices.get v).2 = [p,q])
    (he : p.1 = q.1) : q = (p.1,!p.2) := by
  have hp := marked_endpoint_partition r hr v p q hrow
  have hneq : p ≠ q := by
    have hn := hp.symm.nodup (ends_nodup _)
    exact fun h => (List.nodup_cons.mp hn).1 (by simp [h])
  apply Prod.ext
  · exact he.symm
  · rcases p with ⟨e,a⟩
    rcases q with ⟨f,b⟩
    dsimp at he ⊢
    subst f
    cases a <;> cases b <;> simp_all

 theorem choice_smooth_value (T : Choice.Table K) (r : RawClosedNetwork)
    {s b : ℕ} {arity : ℕ → ℕ} (hr : r.WellFormed s b arity)
    (v : Fin r.vertices.length) (p q : RawEndpoint)
    (hrow : (r.vertices.get v).2 = [p,q])
    (hT : ∀ a b, T (r.vertices.get v).1 [a,b] = Signature.disequality a b) :
    Choice.evaluate T r.edges.length r.vertices =
      (if (smoothAt r v.val p q).circle then 2 else 1) *
        Choice.evaluate T (smoothAt r v.val p q).query.edges.length
          (smoothAt r v.val p q).query.vertices := by
  have hp := marked_endpoint_partition r hr v p q hrow
  have hpbound := (ends_mem _ p).mp (hp.mem_iff.mp (by simp))
  have hqbound := (ends_mem _ q).mp (hp.mem_iff.mp (by simp))
  rw [← Choice.evaluate_perm _ _ (record_partition r v p q hrow)]
  by_cases he : p.1 = q.1
  · have hmate := loop_mate r hr v p q hrow he
    have hrem := (loop_remainder r.edges.length p.1 p.2 (remainderEnds r v.val)
      (by simpa only [hmate] using hp)).2
    conv_lhs => rw [hmate]
    rw [Choice.evaluate_loop T r.edges.length (r.vertices.get v).1 p.1 hpbound p.2
      Signature.disequality (r.vertices.eraseIdx v.val)
      (fun row hv t ht => (hrem t).mp (remainder_member r v.val row hv t ht)) hT]
    simp only [smoothAt,if_pos he,emit,List.length_eraseIdx_of_lt hpbound]
    simp [Signature.disequality,Choice.mapRows,one_add_one_eq_two]
  · rw [Choice.evaluate_splice T r.edges.length (r.vertices.get v).1 p q
      (r.vertices.eraseIdx v.val) hpbound hqbound he (by
        intro row hv t ht
        have hm := remainder_member r v.val row hv t ht
        exact ⟨(ends_mem _ t).mp (hp.mem_iff.mp (by simp [hm])),
          remainder_ne _ p q _ hp t hm⟩) hT]
    simp [smoothAt,he,emit,List.length_eraseIdx_of_lt hqbound,Choice.mapRows]

/-- The exact loop multiplier is part of the returned raw result. -/
theorem raw_smooth_value (T : Choice.Table K) (r : RawClosedNetwork)
    {s b : ℕ} {arity : ℕ → ℕ} (hr : r.WellFormed s b arity)
    (v : Fin r.vertices.length) (p q : RawEndpoint)
    (hrow : (r.vertices.get v).2 = [p,q])
    (hT : ∀ a b, T (r.vertices.get v).1 [a,b] = Signature.disequality a b) :
    RawNative.evaluate T r = (if (smoothAt r v.val p q).circle then 2 else 1) *
      RawNative.evaluate T (smoothAt r v.val p q).query := by
  have hv : ∀ row ∈ r.vertices.eraseIdx v.val, row.1 < s ∧ row.2.length = arity row.1 := by
    intro row hm
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((List.eraseIdx_sublist r.vertices v.val).subset hm)
    rw [← hi]
    exact hr.1 i
  have hout := smoothAt_wellFormed r hr v p q hrow hv
  rw [← evaluate_eq_raw T r hr,← evaluate_eq_raw T _ hout]
  exact choice_smooth_value T r hr v p q hrow hT

end Paper2.BellReduction.NativeSmoothing.Surgery
