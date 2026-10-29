import OnlineSteinerForest.UpperBound.HistoryRepresentatives
import OnlineSteinerForest.UpperBound.HistorySnapshotForest
import OnlineSteinerForest.UpperBound.HistoryBlockVertices

/-! Every live cluster edge lies in its label's actual bought component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem cluster_edge_connected_to_label (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (requests : List (V × V)) (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2)
    (i : ℕ) (hi : i ≤ requests.length) (C : LabeledCluster ℕ)
    (hC : C ∈ (greedyHistory G c requests feasible i).active)
    (u v : V) (he : s(u, v) ∈ clusterEdges G c requests feasible C) :
    (SimpleGraph.fromEdgeSet (boughtBefore G c requests feasible i : Set (Sym2 V))).Reachable
      (requestSource requests u C.label) u ∧
    (SimpleGraph.fromEdgeSet (boughtBefore G c requests feasible i : Set (Sym2 V))).Reachable
      (requestSource requests u C.label) v := by
  obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
  have hjlt := greedyHistory_snapshot_members G c requests feasible i C (Or.inl hC) j hj
  have hlabel := (greedyHistory_invariant G c requests feasible i).partition.label_mem C hC
  have hreach := greedyHistory_members_connected G c requests feasible u i C hC C.label hlabel j hj
  have hjlen : j < requests.length := lt_of_lt_of_le hjlt hi
  rw [requestSource_eq requests u j hjlen] at hreach
  have hedge := purchasedBlock_vertices_connected G c requests feasible ⟨j, hjlen⟩ i hjlt u v he
  exact ⟨hreach.trans hedge.1, hreach.trans hedge.2⟩

end OnlineSteinerForest.UpperBound
