import ComplexCSP.Instances.RootedCSPFunctionalProjection
import ComplexCSP.Instances.RootedCSPCodePresentation
import ComplexCSP.Instances.RootedCSPMachines

/-! # Executable fixed-query recovery of a root functional on raw nonempty codes -/
namespace ComplexCSP.RootedCSPFunctionalRecovery
open PlanarHom PlanarHom.Complexity PairProjectionMachines
open ComplexityCSPCode RootedCSPProjection RootedCSPCodePresentation
open scoped BigOperators
variable {D K : Type} [Fintype D] [Field K] {s : ℕ} {L : Language D K (Fin s)}
variable {w : (Fin 1 → D) → K}

def queries (P : FunctionalData L w) (g : Code) : List Code :=
  (List.ofFn P.gadgets).map (fun Q => query Q g)

theorem fp_queries (P : FunctionalData L w) : FP encoding encoding.list (queries P) :=
  fp_fixedList encoding encoding (List.ofFn P.gadgets) (fun g Q => query Q g) (fun Q _ => fp_query Q)

theorem queries_valid (P : FunctionalData L w) (g : Code) (hg : Valid L g) (hn : 0 < g.vertices)
    (q : Code) (hq : q ∈ queries P g) : Valid L q := by
  obtain ⟨Q,_,rfl⟩ := List.mem_map.mp hq
  rw [←decode_code L g hg hn]
  exact query_valid Q _

theorem recover_queries (P : FunctionalData L w) (g : Code) (hg : Valid L g) (hn : 0 < g.vertices) :
    RootedCSPRecovery.recover P.coefficients ((queries P g).map (partition L)) = rootSum L w g := by
  simp only [queries,List.map_ofFn,RootedCSPRecovery.recover]
  rw [rootSum_decode L g hg hn w,P.correct]
  apply Finset.sum_congr rfl
  intro j _
  rw [←query_partition,decode_code]
  simp

end ComplexCSP.RootedCSPFunctionalRecovery
