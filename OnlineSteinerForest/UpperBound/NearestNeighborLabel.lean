import OnlineSteinerForest.UpperBound.AuxiliaryLabelSequence
import OnlineSteinerForest.UpperBound.NearestNeighborSnapshot

/-! The manuscript nearest-neighbor budget for an actual chronological label batch. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem nearest_neighbor_label_batch (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) :
    ∑ j : Fin n, insertionDistance (lifetimeComponent G c requests feasible fallback label).toSimpleGraph
      (fun e => c (Sym2.map Subtype.val e))
      (lifetimeComponent G c requests feasible fallback label).connected_toSimpleGraph.preconnected
      (labelFarSequence G c hc requests feasible fallback batch label hcard) j ≤
      2 * clusterWeight (blockPayment G c requests feasible) (finalLifetime G c requests feasible label) *
        Real.log ((n + 1 : ℕ) : ℝ) := by
  let i := orderedLabelRequest G c requests feasible batch label hcard ⟨0, by omega⟩
  have hm := (Finset.mem_filter.mp (orderedLabelRequest_mem G c requests feasible batch label hcard ⟨0, by omega⟩)).2
  have hC : IsSnapshot (greedyHistory G c requests feasible requests.length)
      (finalLifetime G c requests feasible label) := by
    have hC' := (finalLifetime_contains_snapshot G c requests feasible (i.val + 1) (by have := i.isLt; omega)
      (requestCluster G c requests feasible i.val) (Or.inl (requestCluster_active G c requests feasible i.val hm.1))).1
    change IsSnapshot _ (finalLifetime G c requests feasible (pairLabel G c requests feasible i.val)) at hC'
    have hl : pairLabel G c requests feasible i.val = label := hm.2.2
    simpa only [hl] using hC'
  exact nearest_neighbor_snapshot G c hc requests feasible requests.length le_rfl
    (finalLifetime G c requests feasible label) hC
    (lifetimeComponent G c requests feasible fallback label)
    (labelFarSequence G c hc requests feasible fallback batch label hcard)

end OnlineSteinerForest.UpperBound
