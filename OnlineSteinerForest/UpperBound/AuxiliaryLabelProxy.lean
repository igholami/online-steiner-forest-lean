import OnlineSteinerForest.UpperBound.OmissionsLabelAlgorithm
import OnlineSteinerForest.UpperBound.AuxiliaryLifetimeWeights
import OnlineSteinerForest.UpperBound.AuxiliaryProxyRealization

/-! Compute the actual nearest earlier proxy and its simple input-graph realizing path. -/
namespace OnlineSteinerForest.UpperBound

variable [OnlineSteinerForest.PathSelection]

open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def labelProxyParent (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (j : Fin n) : Fin (n + 1) :=
  previousIndex j (nearestEarlier (lifetimeComponent G c requests feasible fallback label).toSimpleGraph
    (fun e => c (Sym2.map Subtype.val e))
    (lifetimeComponent G c requests feasible fallback label).connected_toSimpleGraph.preconnected
    (labelFarSequence G c hc requests feasible fallback batch label hcard) j)

noncomputable def labelProxyEdges (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (j : Fin n) : Finset (Sym2 V) :=
  Classical.choose (exists_proxy_realizing_path G (lifetimeGraph G c requests feasible label)
    (lifetimeGraph_le_input G c requests feasible label) c
    (lifetimeComponent G c requests feasible fallback label)
    (labelFarSequence G c hc requests feasible fallback batch label hcard (newIndex j))
    (labelFarSequence G c hc requests feasible fallback batch label hcard
      (labelProxyParent G c hc requests feasible fallback batch label hcard j)))

theorem labelProxyEdges_spec (G : SimpleGraph V) (c : Sym2 V → ℝ)
    (hc : ∀ e ∈ G.edgeSet, 0 < c e) (requests : List (V × V))
    (feasible : ∀ q ∈ requests, G.Reachable q.1 q.2) (fallback : V)
    (batch : Finset (Fin requests.length)) (label : ℕ) {n : ℕ}
    (hcard : (labelBatch G c requests feasible batch label).card = n + 1) (j : Fin n) :
    IsPathEdges G (labelFarSequence G c hc requests feasible fallback batch label hcard (newIndex j)).val
      (labelFarSequence G c hc requests feasible fallback batch label hcard
        (labelProxyParent G c hc requests feasible fallback batch label hcard j)).val
      (labelProxyEdges G c hc requests feasible fallback batch label hcard j) ∧
    edgeCost c (labelProxyEdges G c hc requests feasible fallback batch label hcard j) =
      labelProxyLength G c hc requests feasible fallback batch label hcard j :=
  Classical.choose_spec (exists_proxy_realizing_path G (lifetimeGraph G c requests feasible label)
    (lifetimeGraph_le_input G c requests feasible label) c
    (lifetimeComponent G c requests feasible fallback label)
    (labelFarSequence G c hc requests feasible fallback batch label hcard (newIndex j))
    (labelFarSequence G c hc requests feasible fallback batch label hcard
      (labelProxyParent G c hc requests feasible fallback batch label hcard j)))

end OnlineSteinerForest.UpperBound
