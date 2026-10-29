import OnlineSteinerForest.UpperBound.HistoryMergedComponent
import OnlineSteinerForest.UpperBound.HistoryPrefixConnected

/-! Every request assigned to a new snapshot is internally connected in that snapshot. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem merged_requests_connected (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : Fin requests.length)
    (hp : 0 < blockPayment G c requests feasible i.val)
    (j : ℕ) (hj : j ∈ (MergeHistory.merged i.val
      ((greedyHistory G c requests feasible i.val).active.filter
        (touchesBlock G c requests feasible i.val))).members) (hjlen : j < requests.length) :
    let H := SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible
      (MergeHistory.merged i.val ((greedyHistory G c requests feasible i.val).active.filter
        (touchesBlock G c requests feasible i.val))) : Set (Sym2 V))
    H.Reachable requests[i.val].1 requests[j].1 ∧ H.Reachable requests[i.val].1 requests[j].2 := by
  let C := MergeHistory.merged i.val ((greedyHistory G c requests feasible i.val).active.filter
    (touchesBlock G c requests feasible i.val))
  have hC : C ∈ (greedyHistory G c requests feasible (i.val + 1)).active := by
    change C ∈ (scanHistory _ _ (i.val + 1)).active
    rw [scanHistory, if_pos hp]
    exact Finset.mem_insert_self _ _
  have hconn := greedyHistory_members_connected G c requests feasible requests[i.val].1
    (i.val + 1) C hC i.val (MergeHistory.new_mem_merged _ _) j hj
  rw [requestSource_eq requests requests[i.val].1 i.val i.isLt,
    requestSource_eq requests requests[i.val].1 j hjlen] at hconn
  have hjlt := greedyHistory_snapshot_members G c requests feasible (i.val + 1) C (Or.inl hC) j hj
  have htarget := hconn.trans (request_reachable_after G c requests feasible ⟨j, hjlen⟩ (i.val + 1) hjlt)
  exact ⟨after_component_reachable_in_merged G c hc requests feasible i _ hconn,
    after_component_reachable_in_merged G c hc requests feasible i _ htarget⟩

end OnlineSteinerForest.UpperBound
