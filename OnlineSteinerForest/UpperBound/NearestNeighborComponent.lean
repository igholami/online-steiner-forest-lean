import OnlineSteinerForest.UpperBound.NearestNeighbor
import OnlineSteinerForest.UpperBound.HistorySnapshotForest

/-! Apply the proved insertion estimate inside ordinary mathlib forest components. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Nearest-earlier insertion in any connected component of a forest, using
mathlib's induced connected-component graph. -/
theorem nearest_neighbor_forest_component (F : SimpleGraph V) (hF : F.IsAcyclic)
    (C : F.ConnectedComponent) (c : Sym2 C → ℝ)
    (hc : ∀ e ∈ C.toSimpleGraph.edgeSet, 0 ≤ c e) {n : ℕ} (x : Fin (n + 1) → C) :
    ∑ i : Fin n, insertionDistance C.toSimpleGraph c C.connected_toSimpleGraph.preconnected x i ≤
      2 * edgeCost c C.toSimpleGraph.edgeFinset * Real.log ((n + 1 : ℕ) : ℝ) := by
  exact nearest_neighbor_sum C.toSimpleGraph (hF.isTree_connectedComponent C) c hc x

end OnlineSteinerForest.UpperBound
