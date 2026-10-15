import Counting.Bridge.OpenNetwork.Ordinary
import Counting.Bridge.OpenNetwork.Clients
import Counting.Bridge.OpenNetwork.EdgeCases

open Counting.Bridge.OpenNetwork

example (x : Fin 0 → Bool) :
    (Counting.Bridge.Holant.toOpenInstance
      (ordinaryNetwork EdgeCases.empty (fun j => Fin.elim0 j))).partition x = 1 := by
  rw [← partition_closed, EdgeCases.empty_partition]

example : (toOpenInstance Clients.ordinary).partition (fun _ => false) = 5 := by
  rw [partition_toOpenInstance]
  change (Holant.OpenNetwork.singleVertex _).raw _ = _
  rw [Holant.OpenNetwork.raw_vertex]
  rfl
