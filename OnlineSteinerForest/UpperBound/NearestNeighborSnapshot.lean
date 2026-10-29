import OnlineSteinerForest.UpperBound.NearestNeighborForestCost
import OnlineSteinerForest.UpperBound.HistorySnapshotForest
import OnlineSteinerForest.UpperBound.HistoryPersistence

/-! Nearest-neighbor insertion on an actual greedy lifetime, charged to its payment mass. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem nearest_neighbor_snapshot (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (i : ℕ) (hi : i ≤ requests.length)
    (C : LabeledCluster ℕ) (hC : IsSnapshot (greedyHistory G c requests feasible i) C)
    (K : (SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible C : Set (Sym2 V))).ConnectedComponent)
    {n : ℕ} (x : Fin (n + 1) → K) :
    ∑ j : Fin n, insertionDistance K.toSimpleGraph (fun e => c (Sym2.map Subtype.val e))
      K.connected_toSimpleGraph.preconnected x j ≤
      2 * clusterWeight (blockPayment G c requests feasible) C * Real.log ((n + 1 : ℕ) : ℝ) := by
  let F := SimpleGraph.fromEdgeSet (clusterEdges G c requests feasible C : Set (Sym2 V))
  have hinput : ∀ e ∈ clusterEdges G c requests feasible C, e ∈ G.edgeSet := by
    intro e he
    obtain ⟨j, hj, he⟩ := Finset.mem_biUnion.mp he
    exact purchasedBlock_input G c requests feasible j e he
  have hnonneg : ∀ e ∈ clusterEdges G c requests feasible C, 0 ≤ c e :=
    fun e he => le_of_lt (hc e (hinput e he))
  have hF : ∀ e ∈ F.edgeSet, 0 ≤ c e := by
    intro e he
    have he' : e ∈ (clusterEdges G c requests feasible C : Set (Sym2 V)) \ Sym2.diagSet := by
      simpa only [F, SimpleGraph.edgeSet_fromEdgeSet] using he
    exact hnonneg e he'.1
  have hd : ∀ e ∈ K.toSimpleGraph.edgeSet, 0 ≤ c (Sym2.map Subtype.val e) := by
    intro e
    refine Sym2.ind (fun u v huv => ?_) e
    exact hF s(u.val, v.val) huv
  have htree := greedyHistory_snapshot_forest G c hc requests feasible i C hC
  have hnn := nearest_neighbor_forest_component F htree K _ hd x
  have hcost := (component_graphCost_le F K c hF).trans (graphCost_fromEdgeSet_le _ c hnonneg)
  rw [clusterEdges_cost G c requests feasible C
    (fun j hj => (greedyHistory_snapshot_members G c requests feasible i C hC j hj).trans_le hi)] at hcost
  rw [graphCost_eq_edgeFinset] at hcost
  apply hnn.trans
  have hlog : 0 ≤ Real.log ((n + 1 : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcost (by norm_num)) hlog

end OnlineSteinerForest.UpperBound
