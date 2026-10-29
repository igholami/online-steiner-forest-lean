import OnlineSteinerForest.UpperBound.HistoryMergedRequests

/-! Live snapshots internally connect every request assigned to their component. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem greedyHistory_requests_connected (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) (hi : i ≤ requests.length) :
    ∀ C ∈ (greedyHistory G c requests feasible i).active,
      ∀ (a b : Fin requests.length), a.val ∈ C.members → b.val ∈ C.members →
      (SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible C : Set (Sym2 V))).Reachable
          requests[a.val].1 requests[b.val].1 ∧
      (SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible C : Set (Sym2 V))).Reachable
          requests[a.val].1 requests[b.val].2 := by
  induction i with
  | zero => simp [greedyHistory, scanHistory, MergeHistory.empty]
  | succ i ih =>
    have hi' : i < requests.length := by omega
    intro C hC a b ha hb
    by_cases hp : 0 < blockPayment G c requests feasible i
    · change C ∈ (scanHistory _ _ (i + 1)).active at hC
      rw [scanHistory, if_pos hp] at hC
      rcases Finset.mem_insert.mp hC with rfl | hC
      · have hA := merged_requests_connected G c hc requests feasible ⟨i, hi'⟩ hp a.val ha a.isLt
        have hB := merged_requests_connected G c hc requests feasible ⟨i, hi'⟩ hp b.val hb b.isLt
        exact ⟨hA.1.symm.trans hB.1, hA.1.symm.trans hB.2⟩
      · exact ih (by omega) C (Finset.mem_sdiff.mp hC).1 a b ha hb
    · have hC' : C ∈ (greedyHistory G c requests feasible i).active := by
        simpa [greedyHistory, scanHistory, hp] using hC
      exact ih (by omega) C hC' a b ha hb

end OnlineSteinerForest.UpperBound
