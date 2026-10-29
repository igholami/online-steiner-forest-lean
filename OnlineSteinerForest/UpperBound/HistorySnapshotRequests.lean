import OnlineSteinerForest.UpperBound.HistoryRequestsConnected
import OnlineSteinerForest.UpperBound.HistoryPersistence

/-! Retired lifetimes retain the internal connections proved while they were active. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem retired_requests_connected (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) (hi : i ≤ requests.length) :
    ∀ C ∈ (greedyHistory G c requests feasible i).retired,
      ∀ (a b : Fin requests.length), a.val ∈ C.members → b.val ∈ C.members →
      (SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible C : Set (Sym2 V))).Reachable
          requests[a.val].1 requests[b.val].1 ∧
      (SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible C : Set (Sym2 V))).Reachable
          requests[a.val].1 requests[b.val].2 := by
  induction i with
  | zero => simp [greedyHistory, scanHistory, MergeHistory.empty]
  | succ i ih =>
    intro C hC a b ha hb
    by_cases hp : 0 < blockPayment G c requests feasible i
    · change C ∈ (scanHistory _ _ (i + 1)).retired at hC
      rw [scanHistory, if_pos hp] at hC
      rcases List.mem_append.mp hC with hC | hC
      · have hCa := (Finset.mem_filter.mp (Finset.mem_toList.mp hC)).1
        have hCa := (Finset.mem_filter.mp hCa).1
        exact greedyHistory_requests_connected G c hc requests feasible i (by omega) C hCa a b ha hb
      · exact ih (by omega) C hC a b ha hb
    · have hC' : C ∈ (greedyHistory G c requests feasible i).retired := by
        simpa [greedyHistory, scanHistory, hp] using hC
      exact ih (by omega) C hC' a b ha hb

theorem snapshot_requests_connected (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) (hi : i ≤ requests.length)
    (C : LabeledCluster ℕ) (hC : IsSnapshot (greedyHistory G c requests feasible i) C)
    (a b : Fin requests.length) (ha : a.val ∈ C.members) (hb : b.val ∈ C.members) :
    (SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible C : Set (Sym2 V))).Reachable
        requests[a.val].1 requests[b.val].1 ∧
    (SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible C : Set (Sym2 V))).Reachable
        requests[a.val].1 requests[b.val].2 := by
  rcases hC with hC | hC
  · exact greedyHistory_requests_connected G c hc requests feasible i hi C hC a b ha hb
  · exact retired_requests_connected G c hc requests feasible i hi C hC a b ha hb

end OnlineSteinerForest.UpperBound
